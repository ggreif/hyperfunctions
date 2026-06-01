{-# LANGUAGE OverloadedStrings #-}

-- | Value-level interpreter for the constructor language.
--
--   A small reduction engine for the value-level fragment: variables,
--   ctor applications, lambdas, case expressions.  Produces a normal
--   form (a 'Value') or a stuck term when reduction can't proceed.
--
--   Phase B of the narrowing plan ('.claude/plans/narrowing.md'):
--   standalone module, not yet wired into HypTwr.  Phase C will hook
--   this from HypTwr's 'meet' when a 'TyDeferV' application appears
--   with all-concrete args.  Phase D will extend it with narrowing
--   (case-split on stuck head metas via LogicT).
--
--   For now: pure structural reduction, no metas, no narrowing.
module Constructor.Interp
  ( -- * IR
    Expr (..)
  , Pattern (..)
  , Arm (..)
    -- * Values
  , Value (..)
  , Stuck (..)
    -- * Reduction
  , interp
  , Env
  , Globals
    -- * Tree → Expr translation
  , fromBuild
  , fromDissect
  , extractGlobals
  , extractCtorPaths
  , extractDataCtors
    -- * Bridge: demote / promote / reduce
  , demote
  , promote
  , valueToExpr
  , reduceDeferred
  , normaliseDeferred
    -- * Narrowing
  , narrowOnce
  ) where

import qualified Constructor.AST as AST
import Constructor.AST (Tree)
import Constructor.HyperLite (Hyper, hPure, hRun)
import Constructor.Level (Lv (..))
import Constructor.Path (Path, PathStep (..), extendPath)
import Constructor.Sort (Mode (..), Sort (..))
import Constructor.Syntax (Name)
import Constructor.Tower (KindEnv, kindOf)
import Constructor.TyProc (MetaId (..), Subst, TyView (..), resolveView)
import Data.Kind (Type)
import Data.List (elemIndex)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

-- | Value-level expression — a simplified IR for the interpreter.
--   Built from the constructor's 'Tree' AST by an upcoming carrier
--   (or hand-constructed for testing).
data Expr
  = EVar !Name
  | ECtor !Name ![Expr]
  | ELam !Name !Expr
  | EApp !Expr !Expr
  | ECase !Expr ![Arm]
  | EMeta !MetaId        -- ^ a free type-level sub-meta demoted to value
                          --   level (Phase D-full narrowing): stands for a
                          --   not-yet-known ctor argument.  Reduces to a
                          --   'VStuck (SMeta …)'; pattern-binds and is
                          --   discarded when the arm body ignores it.
  deriving (Eq, Show)

-- | Patterns appearing in case arms.
data Pattern
  = PVar !Name
  | PCtor !Name ![Pattern]
  | PWild
  | PAt !Name !Pattern   -- @-binder: name@inner; binds name to the whole
                          --   matched value AND recurses into inner.
  deriving (Eq, Show)

-- | One arm of a case expression.
data Arm = Arm !Pattern !Expr
  deriving (Eq, Show)

-- | A reduced value, or a stuck term.  The two are distinguished by
--   constructor: 'VCon'/'VClos' are reduced; 'VStuck' carries the
--   stuck-shape so callers (Phase D narrowing) can decide what to
--   do.
data Value
  = VCon !Name ![Value]
  | VClos !Env !Name !Expr
  | VStuck !Stuck
  deriving (Eq, Show)

-- | A stuck term.  Reduction halted because the head can't be reduced
--   (a free variable, a stuck application, a case on a stuck
--   scrutinee).  At Phase B these are just observed and returned;
--   Phase D will case-split on 'SCase' with a 'VCon'-ctor scrutinee.
data Stuck
  = SVar !Name
  | SMeta !MetaId         -- ^ a free type-level sub-meta carried through
                           --   reduction (Phase D-full); holds the 'MetaId'
                           --   directly (paths intact, no stringification).
  | SApp !Value !Value
  | SCase !Value ![Arm]
  deriving (Eq, Show)

-- | Lexical environment: name-to-value bindings introduced by lambdas
--   and pattern-binders.
type Env = Map Name Value

-- | Top-level definitions: name-to-Expr bindings for the program's
--   let-decls.  Looked up by 'EVar' when the env doesn't have the
--   name locally.
type Globals = Map Name Expr

-- | The reduction engine.  Walks the expression, reducing applications
--   against closures, dispatching cases against ctor scrutinees, and
--   chasing variables through the env-then-globals lookup chain.
--
--   Produces a 'Value' that is either:
--
--     * 'VCon n args' — a normal ctor value (args are also reduced),
--     * 'VClos env x body' — an unapplied closure (lambda),
--     * 'VStuck s' — reduction halted at an irreducible term.
interp :: Globals -> Env -> Expr -> Value
interp gs env e = case e of
  EVar n -> case Map.lookup n env of
    Just v  -> v
    Nothing -> case Map.lookup n gs of
      Just body -> interp gs Map.empty body
      Nothing   -> VStuck (SVar n)

  ECtor n args -> VCon n (map (interp gs env) args)

  ELam x body -> VClos env x body

  EMeta m -> VStuck (SMeta m)

  EApp f a -> case interp gs env f of
    VClos env' x body -> interp gs (Map.insert x va env') body
      where va = interp gs env a
    VCon n vs -> VCon n (vs <> [interp gs env a])
    VStuck s  -> VStuck (SApp (VStuck s) (interp gs env a))

  ECase scrut arms -> case interp gs env scrut of
    VCon sn sargs -> tryArms sn sargs arms
    other         -> VStuck (SCase other arms)
  where
    -- Try each arm against a fully-reduced ctor scrutinee.
    -- First match wins; binders introduced by the pattern flow
    -- into the body's env via 'matchPattern'.
    tryArms _  _     []                  = VStuck (SCase (VCon "<unreached>" []) [])
    tryArms sn sargs (Arm pat body : rest) =
      case matchPattern pat (VCon sn sargs) of
        Just bindings -> interp gs (bindings <> env) body
        Nothing       -> tryArms sn sargs rest

-- | Match a pattern against a value; on success, return the bindings
--   the pattern introduces.  'Nothing' means the pattern's shape
--   doesn't match (try the next arm).
matchPattern :: Pattern -> Value -> Maybe Env
matchPattern pat v = case (pat, v) of
  (PWild, _) -> Just Map.empty
  (PVar n, _) -> Just (Map.singleton n v)
  (PAt n inner, _) -> do
    innerBinds <- matchPattern inner v
    pure (Map.insert n v innerBinds)
  (PCtor pn ps, VCon vn vs)
    | pn == vn && length ps == length vs ->
        mconcat <$> traverse (uncurry matchPattern) (zip ps vs)
  _ -> Nothing

-- ---------------------------------------------------------------------
-- Tree → Expr translation
-- ---------------------------------------------------------------------

-- | Convert a Build-mode 'Tree' AST node to an 'Expr'.  Sort-indexed
--   GADT pattern-match keeps this exhaustive: only ctors that can
--   inhabit @'SVal 'Build@ appear.
fromBuild :: forall (a :: Sort -> Type). Tree a ('SVal 'Build) -> Expr
fromBuild t = case t of
  AST.ValVar _ n _       -> EVar n
  AST.ValCtor _ n _ args -> ECtor n (map fromBuild args)
  AST.ValLam _ n _ body  -> ELam n (fromBuild body)
  AST.ValApp _ _ f x     -> EApp (fromBuild f) (fromBuild x)
  AST.Case _ scrut arms  -> ECase (fromBuild scrut) (map fromArm arms)
  where
    fromArm :: Tree a 'SArm -> Arm
    fromArm (AST.Arm _ pat body) = Arm (fromDissect pat) (fromBuild body)

-- | Convert a Dissect-mode 'Tree' AST node (pattern position) to a
--   'Pattern'.  Sort-indexed; only ctors that can inhabit
--   @'SVal 'Dissect@ appear.
fromDissect :: forall (a :: Sort -> Type). Tree a ('SVal 'Dissect) -> Pattern
fromDissect t = case t of
  AST.ValVar _ n _       -> PVar n
  AST.ValWild _          -> PWild
  AST.ValCtor _ n _ args -> PCtor n (map fromDissect args)
  AST.ValAt _ n _ inner  -> PAt n (fromDissect inner)

-- | Walk a program's top-level decls and harvest each 'ValDecl' as a
--   'Globals' entry mapping its binder name to the body's 'Expr'.
--   Other decl shapes (data declarations, ctor declarations) are
--   skipped — they don't contribute value-level bindings.
extractGlobals :: forall (a :: Sort -> Type). Tree a 'SProg -> Globals
extractGlobals (AST.Prog _ ds) = foldr collect Map.empty ds
  where
    collect :: Tree a 'SDecl -> Globals -> Globals
    collect d gs = case d of
      AST.ValDecl _ _ name body -> Map.insert name (fromBuild body) gs
      _                         -> gs

-- | Harvest all ctor declarations' decl-paths from a program's tree.
--   Walks each 'DataDecl' and its body of 'CtorDecl's, deriving each
--   ctor's path by extending the data's path with 'PsDeclIdx' for
--   the ctor's position.  Used by 'promote' to reconstruct TyView
--   shapes from interpreter Values.
extractCtorPaths :: forall (a :: Sort -> Type). Tree a 'SProg -> Map Name Path
extractCtorPaths (AST.Prog _ ds) = foldr collectProg Map.empty ds
  where
    collectProg :: Tree a 'SDecl -> Map Name Path -> Map Name Path
    collectProg (AST.DataDecl _ dataPath _ _ _ ctors) cps =
      foldr (collectCtor dataPath) cps (zip [0 :: Int ..] ctors)
    collectProg _ cps = cps

    collectCtor :: Path -> (Int, Tree a 'SDecl) -> Map Name Path -> Map Name Path
    collectCtor dataPath (i, AST.CtorDecl _ name _) cps =
      Map.insert name (extendPath (PsDeclIdx i) dataPath) cps
    collectCtor _ _ cps = cps

-- | Harvest the ctor list (with arity) per data type from the
--   program's tree.  For 'Nat⋮ { Z⋮; S Nat⋮ }' produces
--   @{ "Nat" |-> [("Z", 0), ("S", 1)], "Z" |-> [("Z", 0)] }@:
--   the data type itself maps to its ctors, plus each nullary
--   ctor gets a singleton-entry mapping its own name to itself
--   (the ⋮-sugar makes Z : Z, so a meta of type Z is inhabited
--   only by Z itself).  Arity is computed by counting arrows in
--   the ctor's type signature.
extractDataCtors :: forall (a :: Sort -> Type). Tree a 'SProg -> Map Name [(Name, Int)]
extractDataCtors (AST.Prog _ ds) =
  let -- Each ctor is also its own iso-tower singleton "data": the
      -- type 'C'-headed has sole ctor-shape 'C' at its own arity.
      -- Nullary 'Z' → 'Z' ↦ [(Z,0)]; unary 'S' → 'S' ↦ [(S,1)].
      -- Narrowing (Phase D) enumerates these when an arg's expected
      -- type heads on a ctor (e.g. a single-arm 'case n { S m -> … }'
      -- pins the parameter to the 'S'-headed singleton).
      baseMap     = foldr collectProg Map.empty ds
      singletons  = Map.fromList
        [ (cname, [(cname, ar)])
        | (_, ctors) <- Map.toList baseMap
        , (cname, ar) <- ctors
        ]
  in Map.union baseMap singletons
  where
    collectProg :: Tree a 'SDecl -> Map Name [(Name, Int)] -> Map Name [(Name, Int)]
    collectProg (AST.DataDecl _ _ dname _ _ ctors) acc =
      let ctorInfo = [ (cname, countArrows ty)
                     | AST.CtorDecl _ cname ty <- ctors
                     ]
      in Map.insert dname ctorInfo acc
    collectProg _ acc = acc

    -- | Count arrows in a type expression to derive ctor arity.
    --   'Nat' alone (no arrow) → 0; 'Nat -> Nat' → 1; 'Nat -> Nat ->
    --   Nat' → 2.  Also peels '∀'-binders introduced by the ctor
    --   '⋮' sugar; those carry no arity weight (they're binder
    --   intro, not function arrows).
    countArrows :: Tree a 'SExpr -> Int
    countArrows e = case e of
      AST.Arr _ _ b      -> 1 + countArrows b
      AST.ForallLv _ _ _ b -> countArrows b
      _                  -> 0

-- ---------------------------------------------------------------------
-- Bridge: TyView ↔ Value via the ⋮-iso
-- ---------------------------------------------------------------------

-- | Demote a 'TyView' to an interpreter 'Value', when the view is a
--   fully-ctor-headed structure.  Returns 'Nothing' for stuck shapes
--   (TyMetaV, TyDeferV, TyVarV, TyArrV, TyUnivV).
--
--   'TyConV' / 'TyAppV' chains rooted at a 'TyConV' demote to a
--   'VCon' with the head's name and recursively-demoted args.
demote :: Subst -> TyView -> Maybe Value
demote s = go . resolveView s
  where
    go v = case v of
      TyConV n _ _ -> Just (VCon n [])
      TyAppV{}     -> do
        (headName, argViews) <- peelCtorChain v
        VCon headName <$> traverse (demote s) argViews
      -- A free sub-meta (Phase D-full): carry it as a stuck value.
      -- The interpreter pattern-binds it; arms that ignore it reduce
      -- to a ground result, arms that need it leave the result stuck
      -- (→ promote fails → that narrowing candidate is rejected).
      TyMetaV mid  -> Just (VStuck (SMeta mid))
      _            -> Nothing

    peelCtorChain :: TyView -> Maybe (Name, [TyView])
    peelCtorChain = peel []
      where
        peel acc t = case resolveView s t of
          TyConV n _ _  -> Just (n, acc)
          TyAppV f x    -> peel (hRun x : acc) (hRun f)
          _             -> Nothing

-- | Promote a 'Value' to a 'TyView'.  Requires a @Map Name Path@ of
--   ctor → decl-path to reconstruct 'TyConV' shapes.  Returns
--   'Nothing' for non-ctor Values (closures, stuck) or for ctor
--   names absent from the ctor-paths map.
promote :: Map Name Path -> Value -> Maybe TyView
promote cps = go
  where
    go v = case v of
      VCon n args -> do
        ctorPath <- Map.lookup n cps
        argViews <- traverse go args
        pure (mkAppChain (TyConV n ctorPath Z) argViews)
      _ -> Nothing  -- VClos / VStuck — can't promote

    mkAppChain :: TyView -> [TyView] -> TyView
    mkAppChain head_ []     = head_
    mkAppChain head_ (a:as) = mkAppChain (TyAppV (hPure head_) (hPure a)) as

-- | Convert a fully-reduced 'Value' back to an 'Expr'.  Used when
--   feeding demoted arguments into 'interp' via 'EApp'.  Returns
--   'Nothing' for stuck/closure shapes — those can't be re-used as
--   ctor-arg expressions.
valueToExpr :: Value -> Maybe Expr
valueToExpr v = case v of
  VCon n args        -> ECtor n <$> traverse valueToExpr args
  VStuck (SMeta m)   -> Just (EMeta m)   -- round-trip a free sub-meta
  _                  -> Nothing

-- | The core bridge operation: given a deferred-head name and its
--   args (as 'TyView's), demote → interp → promote.  Returns
--   'Nothing' if any step fails:
--
--     * Args fail the slidability gate (Phase 3 of the iso-tower-
--       parametric arc): every arg must be a ctor application
--       (head registered in 'ctorPaths').  Non-ctor tycons (e.g.
--       a bare classical type 'Bool') block the slide here, even
--       though they would structurally demote to a 'VCon'.
--     * Args don't fully demote (some still have metas / deferred).
--     * Function name not in 'Globals'.
--     * Interpreter produces a stuck/closure value (incomplete or
--       inapplicable).
--     * Result Value can't promote (ctor path unknown).
reduceDeferred
  :: Globals -> Map Name Path -> KindEnv -> Subst
  -> Name -> [TyView] -> Maybe TyView
reduceDeferred gs cps kEnv subst fname argViews = do
  guardSlidable (all (isSlidable kEnv subst) argViews)
  body     <- Map.lookup fname gs
  argVals  <- traverse (demote subst) argViews
  argExprs <- traverse valueToExpr argVals
  let applied = foldl EApp body argExprs
      result  = interp gs Map.empty applied
  case result of
    VCon{} -> promote cps result
    _      -> Nothing
  where
    guardSlidable True  = Just ()
    guardSlidable False = Nothing

-- | An argument is "slidable" iff its kind (via 'kindOf') is
--   self-referential / iso-tower-shaped.  Classical-kinded args
--   ('TyUnivV') block here even when they structurally demote.
--
--   R2 (v0.5.0): switched from structural 'ctorPaths' lookup to
--   a real kind-level check.  'KindEnv' now tracks ctor kinds (set
--   at 'ctorDecl' time, R2's other half), so 'kindOf' on a ctor
--   application gives a meaningful answer for both iso-tower
--   ('TyConV' self-referential) and classical ('TyUnivV') ctors.
--
--   Iso-tower ctors are slidable; classical ctors are not.
--   Unresolved kind metas and deferred chains conservatively
--   block.
isSlidable :: KindEnv -> Subst -> TyView -> Bool
isSlidable kEnv s v = case kindOf s kEnv v of
  TyConV{}    -> True   -- nullary iso-tower (self-ref)
  TyAppV{}    -> True   -- parametric iso-tower (self-applied)
  TyUnivV{}   -> False  -- sticky classical
  TyMetaV{}   -> False  -- conservative on unresolved kind
  TyDeferV{}  -> False  -- nested deferred chain
  TyVarV{}    -> False  -- type variable
  TyArrV{}    -> False  -- function type
  TyCaseV{}   -> False  -- conservative — case-of resolution is future

-- | One level of narrowing on a 'TyAppV' chain rooted at a
--   'TyDeferV' head: for each meta argument, enumerate the
--   constructors the deferred function actually pattern-matches on,
--   and return all (refined-subst, reduced-result) pairs.
--
--   The candidate ctors come from the function's own @case@ arms
--   (read out of its 'Expr' body in 'Globals'), not from the
--   argument's declared type.  This is exactly the set that could
--   make the deferred application reduce — any other ctor hits no
--   arm and goes stuck — so it is both precise (no wasted branches)
--   and disjunctive (a multi-arm function yields one candidate per
--   arm, the list monad serving as the branch bag).
--
--   For an arity-k arm pattern @C p1 … pk@, mint k fresh sub-metas
--   (no gensym — their 'MetaId's extend the narrowed meta's paths
--   with 'PsCtorAppArg i') and build the refined arg as the 'TyAppV'
--   spine @C ?m1 … ?mk@.  Nullary arms (k=0) give a bare 'TyConV'.
--   Free sub-metas ride through the demote/interp/promote bridge as
--   'SMeta' (see 'demote'); an arm body that ignores them reduces to
--   a ground result, one that needs them leaves the result stuck so
--   'promote' rejects that candidate.
--
--   The caller (HypTwr's 'meetNorm') uses this when standard
--   normalisation fails to reduce: try each candidate refinement,
--   pick the first whose result unifies with the other side.
narrowOnce
  :: Globals
  -> Map Name Path                       -- ^ ctor → decl-path
  -> KindEnv                             -- ^ for the kind-level slidability gate
  -> Subst
  -> Name -> [TyView]                    -- ^ deferred function + arg views
  -> [(Subst, TyView)]                   -- ^ candidate (refined-subst, result) pairs
narrowOnce gs cps kEnv subst fname argViews = do
  -- For each arg position, decide: concrete (pass through) or a free
  -- meta to narrow against the function's arm patterns at that
  -- position.  Each yields a (Subst-extension, refined arg view).
  refinements <- mapM (uncurry narrowArg) (zip [0 ..] argViews)
  let combinedSubst = foldr (\(s, _) acc -> Map.union s acc) subst refinements
      refinedArgs   = map snd refinements
  reduced <- maybeToList (reduceDeferred gs cps kEnv combinedSubst fname refinedArgs)
  pure (combinedSubst, reduced)
  where
    -- | Per-arg narrowing decision, by argument position.
    narrowArg :: Int -> TyView -> [(Subst, TyView)]
    narrowArg argIdx argView =
      case resolveView subst argView of
        -- Already concrete: pass through with identity subst.
        v@TyConV{} -> [(Map.empty, v)]
        v@TyAppV{} -> [(Map.empty, v)]
        -- A free meta: enumerate the ctors the function matches on at
        -- this position; one branch per arm.
        TyMetaV (MetaId bp up) -> do
          (cname, arity) <- armCtors gs fname argIdx
          ctorPath       <- maybeToList (Map.lookup cname cps)
          let subMetas = [ TyMetaV (MetaId (extendPath (PsCtorAppArg i) bp)
                                           (extendPath (PsCtorAppArg i) up))
                         | i <- [0 .. arity - 1] ]
              ctorView = foldl (\h a -> TyAppV (hPure h) (hPure a))
                               (TyConV cname ctorPath Z) subMetas
              substExt = Map.singleton (MetaId bp up) ctorView
          pure (substExt, ctorView)
        -- Other shapes (TyArrV, TyUnivV, TyVarV, TyDeferV): skip.
        _ -> []

    maybeToList :: Maybe a -> [a]
    maybeToList Nothing  = []
    maybeToList (Just x) = [x]

-- | The constructors a function pattern-matches on at argument
--   position @argIdx@ — read from its 'Expr' body in 'Globals'.
--   For @\\x0 … xk -> case xj { C1 … -> …; C2 … -> … }@ this is
--   @[(C1, arity1), (C2, arity2), …]@ when @argIdx == j@, else @[]@.
--   Non-'PCtor' arms (wildcards, var binders) are skipped — they
--   match any ctor and so give narrowing nothing to enumerate.
armCtors :: Globals -> Name -> Int -> [(Name, Int)]
armCtors gs fname argIdx = case Map.lookup fname gs of
  Nothing   -> []
  Just body ->
    let (params, inner) = peelLams body
    in case inner of
         ECase (EVar v) arms
           | Just j <- elemIndex v params, j == argIdx ->
               [ (c, length ps) | Arm (PCtor c ps) _ <- arms ]
         _ -> []
  where
    peelLams (ELam x b) = let (xs, e) = peelLams b in (x : xs, e)
    peelLams e          = ([], e)

-- | Walk a 'TyView' recursively, attempting to reduce any
--   'TyAppV'-chain rooted at a 'TyDeferV' head.  Successful
--   reductions replace the chain with the resulting concrete
--   'TyView'; unreachable / partial sub-views are left intact.
--
--   Idempotent on fully-reduced views.  Applied before unification
--   (in 'meet') so 'TyDeferV' applications either resolve to their
--   computed value or stay deferred for Phase D narrowing.
normaliseDeferred
  :: Globals -> Map Name Path -> KindEnv -> Subst -> TyView -> TyView
normaliseDeferred gs cps kEnv subst = go
  where
    go v = case resolveView subst v of
      TyAppV f x -> case peelDeferredHead (TyAppV f x) of
        Just (fname, argViews) ->
          case reduceDeferred gs cps kEnv subst fname argViews of
            Just reduced -> reduced
            Nothing -> TyAppV (mapProc f) (mapProc x)
        Nothing -> TyAppV (mapProc f) (mapProc x)
      TyArrV a b -> TyArrV (mapProc a) (mapProc b)
      other -> other

    mapProc :: Hyper TyView TyView -> Hyper TyView TyView
    mapProc p = hPure (go (hRun p))

    peelDeferredHead :: TyView -> Maybe (Name, [TyView])
    peelDeferredHead = peel []
      where
        peel acc t = case resolveView subst t of
          TyDeferV n _    -> Just (n, acc)
          TyAppV f x      -> peel (hRun x : acc) (hRun f)
          _               -> Nothing
