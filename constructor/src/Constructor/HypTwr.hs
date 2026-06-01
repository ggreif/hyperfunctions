{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}

-- | B-side type inference with 'Tower' as the carrier value at the
--   'SExpr' sort — the four-commit Tower arc's step 4.  Parallel
--   sibling of 'Constructor.HypTinf'.
--
--   Where 'HypTinf' parks each elaborated type as a 'TyProc' (a
--   hyperfunction-of-TyView) and the up-tower is computed on demand
--   via 'liftTower' / 'towerOfView', 'HypTwr' emits a 'Tower'
--   directly.  Each carrier value at 'SExpr' is its own up-tower:
--   the horizontal slot is the parametric content (groupoid-flavoured
--   layer, subject to 'meet'), the vertical slot is the directed @:@
--   step generated coinductively by 'kindOf'.
--
--   Expressive power is the same as 'HypTinf' at the horizontal
--   layer (the 'TyView'-shape is identical); the gain is that the
--   tower structure is *first-class in the carrier value* — every
--   method emits a fully-formed (lazily-unfolded) tower, no later
--   lifting step is required.  This is the seam where the eventual
--   Weird-style self-stratification ('data Weird : Weird') will land:
--   adding a level offset to 'TyConV' will give 'kindOf' a productive
--   way to walk the upper rungs without producing a stationary
--   stream, and the kind-coherence machinery in 'meetTowers' will
--   stabilise via a deck-shift base case rather than the current
--   '*n'-tail one.
--
--   For commit-4 scope the parametric-instantiation customer that
--   'HypTinf.app' runs (allocate a meta per parametric tycon
--   position, unify with the supplied argument, record the binding
--   in 'Subst') is intentionally omitted — the corpus's parametric
--   shape extracts identically with or without it, and the meta
--   layer can be retrofitted alongside the future occurs-check work.
module Constructor.HypTwr
  ( HypTwr
  , HypTwrVal (..)
  , HypTwrResult (..)
  , hypTwrProgram
  , hypTwrProgramWith
  , hypTwrProgramWithCtors
  , hypTwrCtorTypes
  , CtorSig (..)
  , extractCtorSig
  ) where

import Constructor.HyperLite (hPure, hRun)
import Constructor.Interp (Globals, narrowOnce, normaliseDeferred)
import Constructor.Level (Lv (..), starLevel)
import Constructor.Path (Path, PathStep (..), emptyPath, extendPath)
import Constructor.Sort (Mode (..), Sort (..))
import Constructor.Syntax (Lang (..), Name)
import Constructor.Tinf (TyErr (..))
import Constructor.Tower
  ( Tower
  , Gamma (..)
  , meetTowers
  , towerOfView
  )
import Constructor.TyExpr (TyExpr)
import Constructor.TyProc
  ( MetaId (..)
  , Subst
  , TyProc
  , TyView (..)
  , emptySubst
  , materialize
  , meet
  , mkMeta
  , resolveView
  )
import Control.Monad (foldM)
import Data.Kind (Type)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

-- | Per-sort carrier value.  'SExpr' carries a 'Tower' directly; the
--   ctor decl slot pairs the ctor's name with its tower; the data
--   decl slot is 'Nothing' (matching 'HypTinf').
--
--   Value-level carriers ('SVal') carry the term's inferred type as
--   a 'Tower'.  In Build mode this is the expression's result type;
--   in Dissect mode this is the pattern's /matched/ type (the shape
--   the scrutinee must have for the pattern to fire).
--
--   Arm carriers carry @Maybe Tower@: 'Just t' marks the arm as
--   reachable with body type @t@; 'Nothing' marks the arm as
--   unreachable (its pattern's matched type clashed with the
--   scrutinee's type — a coverage observation, not a type error).
--   'case_' filters body towers to the 'Just'-marked arms only.
data HypTwrVal (s :: Sort) where
  HypTwrExpr  :: !Tower                       -> HypTwrVal 'SExpr
  HypTwrDecl  :: !(Maybe (Name, Tower))       -> HypTwrVal 'SDecl
  HypTwrProg  ::                                  HypTwrVal 'SProg
  HypTwrSVal  :: !Tower                       -> HypTwrVal ('SVal m)
  HypTwrSArm  :: !(Maybe Tower)               -> HypTwrVal 'SArm

-- | Elaboration mode for value-level constructs.  The 'Lang' typeclass's
--   'SVal' phantom (a type-level 'Mode') tracks Build / Dissect
--   statically at the surface, but the 'HypTwr' instance dispatches on
--   /runtime/ state because methods like 'valVar' are mode-polymorphic
--   at the Lang level — same impl serves both Build (look up) and
--   Dissect (introduce).
data ElabMode = ElabBuild | ElabDissect
  deriving (Eq, Show)

data HypTwrEnv = HypTwrEnv
  { hypTwrEnvDataTypes :: !(Map Name Int)
  , hypTwrEnvKindEnv   :: !(Map Name TyProc)
    -- ^ Re-used directly with 'Constructor.Tower.kindOf'; the kind
    --   annotation of each declared tycon, captured at 'dataDecl'
    --   elaboration time.
  , hypTwrEnvCtors     :: !(Map Name Tower)
  , hypTwrEnvSubst     :: !Subst
  , hypTwrEnvParent    :: !(Maybe (Name, Path))
  , hypTwrEnvValVars   :: !(Map Name Tower)
    -- ^ Names currently bound at the value level (top-level 'let'
    --   binders, plus pattern-introduced binders inside an arm
    --   body), each paired with its inferred type ('Tower').
    --   For let binders the tower is the RHS's Build-mode type;
    --   for pattern-introduced binders today the tower is a fresh
    --   meta (Dissect-side typing happens next sub-commit, when
    --   the scrutinee's type flows in to refine the meta).
  , hypTwrEnvValPaths  :: !(Map Name Path)
    -- ^ The decl path of each top-level let binding.  Used by the
    --   slide-down rule in 'var' to construct a 'TyDeferV' that
    --   identifies the binding by its source location.  Populated
    --   alongside 'hypTwrEnvValVars' in 'valDecl'.  Pattern
    --   binders don't populate this — only top-level lets, since
    --   only top-level bindings are slideable at type level.
  , hypTwrEnvGlobals   :: !Globals
    -- ^ Value-level bodies of all top-level let-bindings, in
    --   'Interp.Expr' form.  Pre-computed from the Tree AST before
    --   HypTwr elaboration starts (via 'hypTwrProgramWith').  Used
    --   by the bridge ('Interp.reduceDeferred') to evaluate
    --   'TyDeferV' applications during 'meet' normalisation.
  , hypTwrEnvCtorPaths :: !(Map Name Path)
    -- ^ Ctor → decl-path map, also pre-computed from the Tree.
    --   Used by 'Interp.promote' to reconstruct 'TyConV' shapes
    --   from Values when 'reduceDeferred' succeeds.
  , hypTwrEnvDataCtors :: !(Map Name [(Name, Int)])
    -- ^ Per-data-type ctor list (with arity), pre-computed from
    --   the Tree.  Used by 'Interp.narrowOnce' (Phase D) to
    --   enumerate ctor possibilities for a meta argument of a
    --   given data type.
  , hypTwrEnvMode      :: !ElabMode
    -- ^ Runtime mode: 'ElabBuild' (the default) flips to
    --   'ElabDissect' while elaborating an arm's pattern, and
    --   back to 'ElabBuild' for its body.  Read by 'valVar' to
    --   decide whether a name introduces a binder or resolves a
    --   reference.
  , hypTwrEnvScrutTy   :: !(Maybe Tower)
    -- ^ The scrutinee's tower, set by 'case_' for each arm and
    --   consulted by 'arm' to unify against the pattern's
    --   matched type.  'Nothing' outside a case (so a stray
    --   pattern would have no expected type to meet against —
    --   not constructable today since 'arm' only fires inside
    --   a 'case_').
  }

emptyHypTwrEnv :: HypTwrEnv
emptyHypTwrEnv = HypTwrEnv Map.empty Map.empty Map.empty emptySubst Nothing
                            Map.empty Map.empty Map.empty Map.empty Map.empty
                            ElabBuild Nothing

data HypTwrResult = HypTwrResult
  { hypTwrDataTypes :: !(Map Name Int)
  , hypTwrCtors     :: !(Map Name Tower)
  , hypTwrSubst     :: !Subst
  , hypTwrValVars   :: !(Map Name Tower)
    -- ^ Value-level binders defined at the program scope, paired
    --   with their inferred 'Tower' types.
  }

-- | Extract each ctor's first-rung 'TyExpr' from a 'HypTwrResult'.
--   For Tower-meta-free ctors this is the parity invariant against
--   'HypTinf.hypTinfCtorTypes' — both produce the same 'Map Name
--   TyExpr' on the metavariable-free corpus, viewed through their
--   respective extractors.
hypTwrCtorTypes :: HypTwrResult -> Either TyErr (Map Name TyExpr)
hypTwrCtorTypes r = traverse (materialize (hypTwrSubst r) . horizontal)
                             (hypTwrCtors r)

newtype HypTwr (a :: Sort -> Type) (s :: Sort) = HypTwr
  { runHypTwr :: HypTwrEnv -> Either TyErr (HypTwrVal s, HypTwrEnv) }

hypTwrProgram :: HypTwr a 'SProg -> Either TyErr HypTwrResult
hypTwrProgram = hypTwrProgramWith Map.empty Map.empty

-- | Run HypTwr elaboration with pre-populated 'Globals' (value-level
--   bodies of top-level let-bindings) and ctor-paths.  Used by
--   callers that want demote-interpret-promote bridging for
--   'TyDeferV' applications (the Phase C wiring).  When both maps
--   are empty, behaves identically to 'hypTwrProgram' (no
--   reductions fire because 'normaliseDeferred' has nothing to look
--   up).
hypTwrProgramWith
  :: Globals -> Map Name Path -> HypTwr a 'SProg -> Either TyErr HypTwrResult
hypTwrProgramWith gs cps = hypTwrProgramWithCtors gs cps Map.empty

-- | Full Phase C+D entry point: also takes 'dataCtors' (per-data
--   ctor list with arities) so narrowing (Phase D) can enumerate
--   ctor possibilities for meta arguments.
hypTwrProgramWithCtors
  :: Globals -> Map Name Path -> Map Name [(Name, Int)]
  -> HypTwr a 'SProg -> Either TyErr HypTwrResult
hypTwrProgramWithCtors gs cps dctors p = do
  let env0 = emptyHypTwrEnv
        { hypTwrEnvGlobals   = gs
        , hypTwrEnvCtorPaths = cps
        , hypTwrEnvDataCtors = dctors
        }
  (_, env) <- runHypTwr p env0
  pure (HypTwrResult
          (hypTwrEnvDataTypes env)
          (hypTwrEnvCtors env)
          (hypTwrEnvSubst env)
          (hypTwrEnvValVars env))

-- | Helper: build the tower for a leaf 'TyView' under the current
--   env's kindEnv and Subst.  The vertical is lazily generated via
--   'kindOf'.
leafTower :: HypTwrEnv -> TyView -> Tower
leafTower env v = towerOfView (hypTwrEnvSubst env) (hypTwrEnvKindEnv env) v

exprTower :: HypTwrVal 'SExpr -> Tower
exprTower (HypTwrExpr t) = t

-- | Per-ctor signature extracted from a 'Tower'.
--
--   For @c : T1 -> T2 -> ... -> Tk -> D r1 r2 ... rm@:
--
--     * 'ctorInputs' is @[T1, T2, ..., Tk]@ — the argument types,
--       in source order.  When a value-side @c v1 v2 ... vk@ is
--       built, each @vi@ must have type @Ti@.
--
--     * 'ctorRefinements' is @[r1, r2, ..., rm]@ — the result-spine
--       arguments, one per parent parameter (in declaration
--       order).  Pattern matching on @c@ refines the scrutinee's
--       parameter values: when matching @c@ produced by @c x y@
--       against a scrutinee of type @D s1 ... sm@, each @si@
--       unifies with the corresponding @ri@.  For nullary parents
--       the list is empty.
--
--   The vars free in 'ctorInputs' / 'ctorRefinements' that came
--   from the parent's parameter list are universally quantified
--   over the ctor's type and become /existentials/ when the ctor
--   is matched on.
data CtorSig = CtorSig
  { ctorInputs      :: ![TyProc]
  , ctorRefinements :: ![TyProc]
  }

-- | Peel a ctor's annotation tower into the parts the saturation
--   check and 'extractCtorSig' both need.  Returns
--   @(inputs, headView, args)@ such that the tower's first rung
--   resolves (under 'Subst') to
--   @inputs[0] -> ... -> inputs[k-1] -> headView args[0] ... args[m-1]@.
peelCtorTower :: Subst -> Tower -> ([TyProc], TyView, [TyProc])
peelCtorTower subst tower = (inputs, headView, args)
  where
    peelArr ins v = case v of
      TyArrV a bProc -> peelArr (a : ins) (resolveView subst (hRun bProc))
      _ -> (reverse ins, v)
    peelApp as v = case v of
      TyAppV fProc x -> peelApp (x : as) (resolveView subst (hRun fProc))
      _ -> (v, as)
    (inputs, resultView) = peelArr [] (resolveView subst (hRun (horizontal tower)))
    (headView, args)     = peelApp [] resultView

-- | Pull a 'CtorSig' out of a ctor's tower under a substitution.
--   Returns 'Nothing' if the result isn't headed by a 'TyConV'
--   (which the saturation check would have caught at declaration
--   time — so for any tower stored in 'hypTwrCtors', this is
--   'Just').  Exposed for downstream consumers (the eventual
--   pattern-matching machinery) without committing to a specific
--   representation in 'HypTwrResult'.
extractCtorSig :: Subst -> Tower -> Maybe CtorSig
extractCtorSig subst tower =
  let (inputs, headView, refinements) = peelCtorTower subst tower
  in case headView of
       TyConV {} -> Just (CtorSig inputs refinements)
       _         -> Nothing

-- | Saturation check for a constructor declaration.
--
--   Acceptance rules on the peeled head:
--
--     * @h == parentName@: arity must equal the parent's arity.
--       This is the GADT shape (@FZ : Fin Z@, @FS : Fin n -> Fin
--       (S n)@ — each ctor's result is the parent applied to
--       exactly its declared parameters).
--
--     * @h /= parentName@: accepted only when the parent has arity
--       0.  This is the singleton-family relaxation (Swap-style:
--       @data Swap : Swap { Left : Right; Right : Left }@) — when
--       the parent has no parameters, sibling-as-result is the
--       covering-space-equivalent shape.  Real GADTs (arity ≥ 1)
--       must point at the parent.
--
--     * Non-'TyConV' result (e.g., result is a parameter
--       'TyVarV', or a universe 'TyUnivV'): rejected
--       unconditionally — the shape doesn't identify a data type.
--
--   Skipped entirely when there's no enclosing parent (top-level
--   'ctorDecl' which the AST currently rejects elsewhere).
checkSaturation :: HypTwrEnv -> Name -> Tower -> Either TyErr ()
checkSaturation env ctorName tower = case hypTwrEnvParent env of
  Nothing -> Right ()
  Just (parentName, _parentPath) ->
    let subst                = hypTwrEnvSubst env
        (_, headView, args)  = peelCtorTower subst tower
        nargs                = length args
        parentArity          = maybe 0 id (Map.lookup parentName (hypTwrEnvDataTypes env))
    in case headView of
         TyConV h _ _
           | h == parentName ->
               if nargs == parentArity
                 then Right ()
                 else Left (TyCtorWrongArity ctorName parentName parentArity nargs)
           | parentArity == 0 -> Right ()
           | otherwise        -> Left (TyCtorWrongHead ctorName parentName h)
         _ -> Left (TyCtorBadResult ctorName)

threadDecls :: [HypTwr a 'SDecl] -> HypTwrEnv -> Either TyErr HypTwrEnv
threadDecls []     env = Right env
threadDecls (d:ds) env = do
  (_, env1) <- runHypTwr d env
  threadDecls ds env1

-- | Thread a list of value-side carriers through the env, sort-
--   polymorphic so the same helper serves arm-thread and ctor-arg
--   threading (and any future value-level node with a list of
--   uniform-sort children).
threadVals :: [HypTwr a s] -> HypTwrEnv -> Either TyErr HypTwrEnv
threadVals []     env = Right env
threadVals (x:xs) env = do
  (_, env1) <- runHypTwr x env
  threadVals xs env1

-- | Walk a list of arms, collecting each arm's @Maybe Tower@
--   reachability marker (used by 'case_' to filter to reachable
--   bodies and pairwise-meet their towers).  Each arm internally
--   restores the env's val-binders to the outer scope, so the
--   accumulator only grows with the threaded 'Subst'.
threadArmsCarrying
  :: [HypTwr a 'SArm] -> HypTwrEnv -> Either TyErr ([Maybe Tower], HypTwrEnv)
threadArmsCarrying []     env = Right ([], env)
threadArmsCarrying (a:as) env = do
  (armVal, env1) <- runHypTwr a env
  let armRes = sArmTower armVal
  (rest, env2) <- threadArmsCarrying as env1
  pure (armRes : rest, env2)

-- | Pairwise meet on the first rung of a list of towers.  Used to
--   force a 'case' expression's arm bodies to agree on a common
--   result type — each successive pair extends the 'Subst' with
--   whatever bindings the meet introduces.
meetAllTowers :: Subst -> [Tower] -> Either TyErr Subst
meetAllTowers s []           = Right s
meetAllTowers s [_]          = Right s
meetAllTowers s (t1:t2:rest) = do
  s' <- meet s (horizontal t1) (horizontal t2)
  meetAllTowers s' (t2 : rest)

-- | Extract the type tower from a value-level carrier.
sValTower :: HypTwrVal ('SVal m) -> Tower
sValTower (HypTwrSVal t) = t

-- | Extract the reachability-tagged body tower from an arm
--   carrier.  'Just t' if the arm reached (body type @t@);
--   'Nothing' if its pattern clashed with the scrutinee.
sArmTower :: HypTwrVal 'SArm -> Maybe Tower
sArmTower (HypTwrSArm t) = t

-- | Build a 'TyView'-app chain: @head[arg0, arg1, ...]@.  Used by
--   value-level ctor application to construct the result type
--   from the parent 'TyConV' plus the (substituted) refinement
--   TyProcs.  For an empty arg list yields the bare head.
mkAppChainView :: TyView -> [TyProc] -> TyView
mkAppChainView h []     = h
mkAppChainView h (a:as) = mkAppChainView (TyAppV (hPure h) a) as

-- | Elaborate one ctor-app argument (whose mode is the
--   ambient runtime 'hypTwrEnvMode') and meet its inferred 'TyProc'
--   against the corresponding (already parent-TyVarV-instantiated)
--   'ctorInput'.  Threads the env through, with the updated
--   'Subst' carrying any bindings the meet introduced.  Used by
--   both Build (where the arg is a value) and Dissect (where the
--   arg is a sub-pattern whose binders get their types this way).
checkValArg
  :: HypTwrEnv -> (HypTwr a ('SVal m), TyProc) -> Either TyErr HypTwrEnv
checkValArg env (arg, input) = do
  (argVal, env1) <- runHypTwr arg env
  let argProc = horizontal (sValTower argVal)
  newSubst <- meetNorm env1 input argProc
  Right (env1 { hypTwrEnvSubst = newSubst })

-- | Normalising 'meet': pre-reduce any 'TyDeferV' applications via
--   the bridge (demote-interpret-promote) before structural
--   unification.  Phase C hook for the concrete-arg case; Phase D
--   fallback when reduction is stuck on a meta.
--
--   Algorithm:
--
--     1. Apply 'normaliseDeferred' to both sides — reduces any
--        'TyAppV' chain rooted at 'TyDeferV' with fully-concrete
--        args.
--     2. Try standard 'meet' on the normalised views.  If it
--        succeeds, done.
--     3. On TyMismatch, attempt Phase D narrowing: walk both views
--        looking for 'TyDeferV'-headed 'TyAppV' chains with meta
--        args; enumerate ctor refinements via 'narrowOnce' for each
--        meta; for each candidate refinement, re-attempt the meet.
--        First successful branch wins.
meetNorm :: HypTwrEnv -> TyProc -> TyProc -> Either TyErr Subst
meetNorm env p1 p2 =
  let s       = hypTwrEnvSubst env
      gs      = hypTwrEnvGlobals env
      cps     = hypTwrEnvCtorPaths env
      dctors  = hypTwrEnvDataCtors env
      fnTypes = Map.map (hRun . horizontal) (hypTwrEnvValVars env)
      v1      = normaliseDeferred gs cps s (hRun p1)
      v2      = normaliseDeferred gs cps s (hRun p2)
  in case meet s (hPure v1) (hPure v2) of
       Right s' -> Right s'
       Left err ->
         -- Phase D: try narrowing on either side's TyDeferV chain.
         let cands1 = candidatesFor gs cps dctors fnTypes s v1
             cands2 = candidatesFor gs cps dctors fnTypes s v2
             attempts =
               [ meet s'' (hPure v1') (hPure v2')
               | (sub1, v1') <- cands1
               , (sub2, v2') <- cands2
               , let s'' = sub2 `Map.union` sub1 `Map.union` s
               ]
         in case [ s' | Right s' <- attempts ] of
              (s' : _) -> Right s'
              []       -> Left err
  where
    -- | Narrowing candidates for a single TyView, with recursion
    --   into children.  For a TyAppV chain rooted at TyDeferV,
    --   return the narrow-once enumeration; otherwise recurse
    --   into TyAppV / TyArrV children so nested deferred-chains
    --   (e.g., the @pickZ ?n@ inside @Eq Z (pickZ ?n)@) surface.
    candidatesFor gs cps dctors fnTypes s v = case resolveView s v of
      TyAppV f x ->
        case peelDeferredHead s (TyAppV f x) of
          Just (fname, argViews) ->
            let opts = narrowOnce gs cps dctors fnTypes s fname argViews
            in if null opts
                 then [(Map.empty, TyAppV f x)]   -- no narrow available
                 else opts
          Nothing ->
            -- Not deferred at this level — recurse into children
            -- so a nested deferred-chain can still be discovered.
            do (sf, vf) <- candidatesFor gs cps dctors fnTypes s (hRun f)
               (sx, vx) <- candidatesFor gs cps dctors fnTypes s (hRun x)
               pure (sf `Map.union` sx, TyAppV (hPure vf) (hPure vx))
      TyArrV a b ->
        do (sa, va) <- candidatesFor gs cps dctors fnTypes s (hRun a)
           (sb, vb) <- candidatesFor gs cps dctors fnTypes s (hRun b)
           pure (sa `Map.union` sb, TyArrV (hPure va) (hPure vb))
      other -> [(Map.empty, other)]

    peelDeferredHead s = peel []
      where
        peel acc t = case resolveView s t of
          TyDeferV n _    -> Just (n, acc)
          TyAppV f x      -> peel (hRun x : acc) (hRun f)
          _               -> Nothing

-- | Shared elaboration of a value-level constructor application,
--   used by 'valCtor' in both modes:
--
--     1. Look the ctor's tower up by name.
--     2. Peel + saturate to find the parent and the static
--        'CtorSig'.
--     3. Allocate one fresh meta per parent param TyVarV
--        appearing in the ctor's inputs or refinements (call-site
--        path keyed, so distinct use sites get distinct metas).
--     4. Substitute throughout inputs and refinements.
--     5. For each arg + substituted input, run 'checkValArg' —
--        elaborates the arg in the ambient mode (Build computes a
--        value's type; Dissect produces a pattern's matched type
--        and binds pattern-introduced binders to fresh metas
--        which the meet then unifies against the substituted
--        input).
--     6. Build the result tower as 'Parent <substituted refs>'.
elabCtorApp
  :: HypTwrEnv -> Name -> Path -> [HypTwr a ('SVal m)]
  -> Either TyErr (Tower, HypTwrEnv)
elabCtorApp env name callPath args = do
  ctorTower <- maybe (Left (TyUnbound name)) Right
                 (Map.lookup name (hypTwrEnvCtors env))
  let subst0           = hypTwrEnvSubst env
      (_, headView, _) = peelCtorTower subst0 ctorTower
  case (extractCtorSig subst0 ctorTower, headView) of
    (Just sig, TyConV pName pPath _)
      | length args /= length (ctorInputs sig) ->
          Left (TyCtorWrongArity name pName
                 (length (ctorInputs sig)) (length args))
      | otherwise -> do
          let tyVars =
                Set.unions (map (collectTyVars subst0) (ctorInputs sig))
                `Set.union`
                Set.unions (map (collectTyVars subst0) (ctorRefinements sig))
              tySubst     = mkFreshSubst tyVars callPath
              substInputs = map (substTyVarsInProc tySubst) (ctorInputs sig)
              substRefs   = map (substTyVarsInProc tySubst) (ctorRefinements sig)
          env' <- foldM checkValArg env (zip args substInputs)
          let resultView  = mkAppChainView (TyConV pName pPath Z) substRefs
              resultTower = leafTower env' resultView
          Right (resultTower, env')
    _ -> Left (TyCtorBadResult name)

-- ----------------------------------------------------------------------
-- TyVarV instantiation for ctor application.
--
-- A ctor's 'CtorSig' references the /parent's parameter names/ via
-- 'TyVarV' (e.g., FS's input @Fin n@ — the @n@ is the parent Fin's
-- formal parameter).  Each value-level use of the ctor is a fresh
-- /instantiation/: the universal n in FS's type becomes a fresh
-- metavariable per call site, and the meet of each arg against the
-- corresponding instantiated input drives the unification.
--
-- 'collectTyVars' harvests every distinct '(Name, Path)' TyVarV in
-- a 'TyProc' (modulo 'Subst' chasing).  'mkFreshSubst' allocates
-- one 'TyProc'-shaped meta per harvested var, keyed on the var's
-- def-path so all uses of the same parent param across inputs and
-- refinements share the same meta.  'substTyVarsInProc' walks a
-- 'TyProc' substituting any 'TyVarV' for the corresponding meta.
-- ----------------------------------------------------------------------

collectTyVars :: Subst -> TyProc -> Set (Name, Path)
collectTyVars subst p0 = goView (resolveView subst (hRun p0))
  where
    goView v = case v of
      TyVarV n pa -> Set.singleton (n, pa)
      TyAppV f x  -> goProc f `Set.union` goProc x
      TyArrV a b  -> goProc a `Set.union` goProc b
      _           -> Set.empty
    goProc p = goView (resolveView subst (hRun p))

mkFreshSubst :: Set (Name, Path) -> Path -> Map (Name, Path) TyProc
mkFreshSubst vars callPath = Map.fromList
  [ ((n, p), mkMeta p callPath) | (n, p) <- Set.toList vars ]

substTyVarsInView :: Map (Name, Path) TyProc -> TyView -> TyView
substTyVarsInView m v = case v of
  TyVarV n p  -> case Map.lookup (n, p) m of
    Just freshProc -> hRun freshProc
    Nothing        -> v
  TyAppV f x  -> TyAppV (substTyVarsInProc m f) (substTyVarsInProc m x)
  TyArrV a b  -> TyArrV (substTyVarsInProc m a) (substTyVarsInProc m b)
  TyConV {}   -> v
  TyMetaV {}  -> v
  TyUnivV {}  -> v
  TyDeferV {} -> v  -- deferred refs are opaque to type-var subst

substTyVarsInProc :: Map (Name, Path) TyProc -> TyProc -> TyProc
substTyVarsInProc m p = hPure (substTyVarsInView m (hRun p))

instance Lang HypTwr where
  prog _ann ds = HypTwr $ \env -> do
    env' <- threadDecls ds env
    pure (HypTwrProg, env')

  dataDecl _ann declPath name params e ds = HypTwr $ \env ->
    case Map.lookup name (hypTwrEnvDataTypes env) of
      Just _  -> Left (TyDuplicateType name)
      Nothing -> do
        (eVal, env0) <- runHypTwr e env
        -- The kind-annotation's tower; its rung-0 horizontal is the
        -- TyView we'll cache in kindEnv (so 'kindOf' for this tycon
        -- returns its kind annotation).
        let kindTower = exprTower eVal
            kindProc  = horizontal kindTower
        -- Tower-aware kind coherence (lifted from HypTinf): if nested
        -- inside another data, this annotation tower must meet the
        -- parent's TyConV-tower coinductively.
        env0' <- case hypTwrEnvParent env0 of
          Nothing -> Right env0
          Just (parentName, parentPath) ->
            let parentTower = leafTower env0 (TyConV parentName parentPath Z)
                memberTower = leafTower env0 (hRun (horizontal kindTower))
            in do
              subst' <- meetTowers (hypTwrEnvKindEnv env0)
                                   (hypTwrEnvSubst env0)
                                   memberTower parentTower
              Right env0 { hypTwrEnvSubst = subst' }
        let env1 = env0'
              { hypTwrEnvDataTypes =
                  Map.insert name (length params) (hypTwrEnvDataTypes env0')
              , hypTwrEnvKindEnv =
                  Map.insert name kindProc (hypTwrEnvKindEnv env0')
              }
            savedParent = hypTwrEnvParent env1
        env2 <- threadDecls ds (env1 { hypTwrEnvParent = Just (name, declPath) })
        pure (HypTwrDecl Nothing, env2 { hypTwrEnvParent = savedParent })

  ctorDecl _ann name e = HypTwr $ \env -> do
    (val, env1) <- runHypTwr e env
    let tower = exprTower val
    case Map.lookup name (hypTwrEnvCtors env1) of
      Just _  -> Left (TyDuplicateCtor name)
      Nothing -> do
        checkSaturation env1 name tower
        let env2 = env1
              { hypTwrEnvCtors = Map.insert name tower (hypTwrEnvCtors env1) }
        Right (HypTwrDecl (Just (name, tower)), env2)

  -- Slide down the hyper-rise: a name unresolved at the type level
  -- (not in tcBinders/tyBinders, so the parser emitted 'var') might
  -- still be bound at the value level by a top-level 'let'.  The
  -- '⋮'-iso bridges value and type rungs for self-towered data, so
  -- a value-level binding lifts cleanly into type position via the
  -- iso pair (arg-side and result-side).  We emit a 'TyDeferV'
  -- marker — Phase A surfaces the binding; Phases B-D wire in the
  -- interpreter + narrowing that actually reduce 'TyAppV (deferred)
  -- args' to a result.  Truly unbound names still error with
  -- TyUnbound.
  var _ann n = HypTwr $ \env ->
    case Map.lookup n (hypTwrEnvValPaths env) of
      Just declPath ->
        Right (HypTwrExpr (leafTower env (TyDeferV n declPath)), env)
      Nothing -> Left (TyUnbound n)

  tyConRef _ann n path = HypTwr $ \env ->
    Right (HypTwrExpr (leafTower env (TyConV n path Z)), env)

  tyParamRef _ann n path = HypTwr $ \env ->
    Right (HypTwrExpr (leafTower env (TyVarV n path)), env)

  star _ann w = HypTwr $ \env ->
    Right (HypTwrExpr (leafTower env (TyUnivV (starLevel w))), env)

  arr _ann a b = HypTwr $ \env -> do
    (va, env1) <- runHypTwr a env
    (vb, env2) <- runHypTwr b env1
    let aProc = horizontal (exprTower va)
        bProc = horizontal (exprTower vb)
        tower = leafTower env2 (TyArrV aProc bProc)
    pure (HypTwrExpr tower, env2)

  -- Application: children's TyView slots are wrapped back as TyProcs
  -- (option-β's horizontal layer stores TyProcs, not Towers).  No
  -- parametric-meta customer at commit-4 scope; the shape extracts
  -- the same as HypTinf on the corpus.
  app _ann _appPath f x = HypTwr $ \env -> do
    (vf, env1) <- runHypTwr f env
    (vx, env2) <- runHypTwr x env1
    let fProc = horizontal (exprTower vf)
        xProc = horizontal (exprTower vx)
        tower = leafTower env2 (TyAppV fProc xProc)
    pure (HypTwrExpr tower, env2)

  forallLv _ann _name _binderPath body = HypTwr $ runHypTwr body
  existsTy _ann _name _binderPath body = HypTwr $ runHypTwr body

  starVar _ann _name _binderPath _offset = HypTwr $ \env ->
    Right (HypTwrExpr (leafTower env (TyUnivV Z)), env)

  -- ------------------------------------------------------------------
  -- Value-level / pattern-match elaboration.
  --
  -- Build-side typing live as of this commit: 'valDecl' bindings
  -- carry types, 'valVar' Build-mode lookups return the bound
  -- type, 'case_' meets all arm-body types pairwise so they agree
  -- on a common result.  Dissect-side typing — unifying the
  -- pattern's structure against the scrutinee's actual type, and
  -- propagating the per-arm refinement substitution — lands in
  -- the next sub-commit.
  --
  -- Today's Dissect carriers therefore emit /placeholder/ towers
  -- (fresh metas); they don't influence Build-side body typing
  -- in any way that breaks the round-trip axioms because all arm
  -- bodies meet pairwise regardless.  When real Dissect typing
  -- lands, the placeholders get replaced with the substituted
  -- shape derived from the scrutinee, and the round-trips
  -- automatically strengthen into refinement-correctness checks.
  --
  -- Build-side ctor application is /not/ fully typed yet for
  -- arity-≥1 parents: the per-use instantiation of parent param
  -- TyVarVs to fresh metas, plus the meet of each arg against
  -- the instantiated 'ctorInputs', requires a TyVarV-substituting
  -- walk that lives in the same commit as Dissect refinement.
  -- For now arity-≥1 ctors return a "Parent applied to fresh
  -- metas" result and skip the input-side meet — sufficient to
  -- keep arm-body types unifying through metavariable binding.
  -- ------------------------------------------------------------------

  -- Recursive 'let': pre-bind the name to a fresh meta-tower so the
  -- body can refer to itself.  After elaboration, meet the body's
  -- actual tower against the pre-binding meta to propagate any
  -- refinements (the body's type pins down the recursive name's
  -- type at all its use sites).  Non-recursive lets are the
  -- degenerate case where the meet is unconstrained.
  valDecl _ann declPath name body = HypTwr $ \env ->
    case Map.lookup name (hypTwrEnvValVars env) of
      Just _  -> Left (TyDuplicateCtor name)
      Nothing -> do
        let preMeta = leafTower env (TyMetaV (MetaId declPath declPath))
            envPre  = env
              { hypTwrEnvValVars =
                  Map.insert name preMeta (hypTwrEnvValVars env) }
        (bodyVal, env1) <- runHypTwr body envPre
        let bodyTower = sValTower bodyVal
        subst' <- meetNorm env1
                            (horizontal preMeta)
                            (horizontal bodyTower)
        let env2 = env1
              { hypTwrEnvValVars =
                  Map.insert name bodyTower (hypTwrEnvValVars env1)
              , hypTwrEnvValPaths =
                  Map.insert name declPath (hypTwrEnvValPaths env1)
              , hypTwrEnvSubst = subst'
              }
        Right (HypTwrDecl Nothing, env2)

  valVar _ann name path = HypTwr $ \env -> case hypTwrEnvMode env of
    ElabBuild ->
      case Map.lookup name (hypTwrEnvValVars env) of
        Just tower -> Right (HypTwrSVal tower, env)
        Nothing    -> Left (TyUnbound name)
    ElabDissect ->
      let metaTower = leafTower env (TyMetaV (MetaId path path))
          env'      = env { hypTwrEnvValVars =
                              Map.insert name metaTower (hypTwrEnvValVars env) }
      in Right (HypTwrSVal metaTower, env')

  valWild _ann = HypTwr $ \env ->
    -- Dissect-only by signature; no binder, no scope mutation.
    -- The placeholder meta uses 'emptyPath' for both slots — a
    -- known sentinel that the next sub-commit replaces with the
    -- pattern position's actual path (Lang.valWild gains a Path
    -- parameter at that point).
    let placeholderTower = leafTower env (TyMetaV (MetaId emptyPath emptyPath))
    in Right (HypTwrSVal placeholderTower, env)

  -- The Build and Dissect branches of 'valCtor' do the same work:
  -- instantiate the ctor's parent-param TyVarVs to fresh metas at
  -- the use site, then meet each arg against the corresponding
  -- instantiated 'ctorInput'.  The two modes differ only in how
  -- args /elaborate/ — Build args produce values' types, Dissect
  -- args (recursively) produce patterns' matched types and bind
  -- pattern-introduced variables.  Each successful meet extends
  -- 'Subst' uniformly.  The pattern's own matched type (Dissect)
  -- and the application's result type (Build) are both
  -- "Parent applied to substituted refinements".
  valCtor _ann name callPath args = HypTwr $ \env -> do
    (resultTower, env') <- elabCtorApp env name callPath args
    Right (HypTwrSVal resultTower, env')

  case_ _ann scrutinee arms = HypTwr $ \env -> do
    (scrutVal, env1) <- runHypTwr scrutinee env
    let scrutTower = sValTower scrutVal
        savedScrut = hypTwrEnvScrutTy env1
        env1'      = env1 { hypTwrEnvScrutTy = Just scrutTower }
    -- Walk arms with scrutinee tower in env.  Each arm either
    -- elaborates reachably (returning 'Just bodyTower') or
    -- marks itself unreachable ('Nothing').
    (armResults, env2) <- threadArmsCarrying arms env1'
    let env3       = env2 { hypTwrEnvScrutTy = savedScrut }
        reachable  = [t | Just t <- armResults]
    -- Pairwise-meet the reachable arms' body towers so the case
    -- agrees on a common result type.  If no arm is reachable,
    -- the case is vacuous — we emit a fresh meta at the case's
    -- own position (not strictly correct as a coverage check,
    -- but harmless until exhaustiveness lands).
    finalSubst <- meetAllTowers (hypTwrEnvSubst env3) reachable
    let env4 = env3 { hypTwrEnvSubst = finalSubst }
        resultTower = case reachable of
          (t:_) -> t
          []    -> leafTower env4
                     (TyMetaV (MetaId emptyPath emptyPath))
    Right (HypTwrSVal resultTower, env4)

  arm _ann pat body = HypTwr $ \env -> do
    let savedVars  = hypTwrEnvValVars env
        savedMode  = hypTwrEnvMode env
        envD       = env { hypTwrEnvMode = ElabDissect }
    (patVal, env1) <- runHypTwr pat envD
    let patTower = sValTower patVal
    -- Unify the pattern's matched type against the scrutinee's
    -- type.  A clean meet means the arm is /reachable/ under
    -- the bindings the meet introduces; a 'TyMismatch' means
    -- the refinement clash discards the arm.  The bindings the
    -- meet produces refine the scrutinee's free metas /and/ the
    -- pattern's binders (which were placeholder metas before
    -- this point) to their respective shape-derived types.
    case hypTwrEnvScrutTy env1 of
      Nothing -> Left (TyUnbound "scrutinee")  -- arm fired outside case_
      Just scrutTower ->
        case meetNorm env1
                  (horizontal patTower)
                  (horizontal scrutTower) of
          Left _ ->
            -- Unreachable arm: skip its body entirely.  Restore
            -- the value-binder scope; preserve the 'Subst' that
            -- existed before the (failed) pattern-side meet,
            -- so subsequent arms aren't poisoned by partial
            -- bindings.
            let env2 = env1
                  { hypTwrEnvValVars = savedVars
                  , hypTwrEnvMode    = savedMode
                  , hypTwrEnvSubst   = hypTwrEnvSubst env  -- pre-pat
                  }
            in Right (HypTwrSArm Nothing, env2)
          Right subst' -> do
            -- Reachable arm: continue with the meet's
            -- bindings, elaborate the body in Build mode.
            let env1' = env1
                  { hypTwrEnvSubst = subst'
                  , hypTwrEnvMode  = ElabBuild
                  }
            (bodyVal, env2) <- runHypTwr body env1'
            let bodyTower = sValTower bodyVal
                env3 = env2
                  { hypTwrEnvValVars = savedVars
                  , hypTwrEnvMode    = savedMode
                  }
            Right (HypTwrSArm (Just bodyTower), env3)

  -- @-binder in Dissect: bind 'name' at the inner pattern's
  -- matched type, leave the at-binder's outward type to be the
  -- inner's (it's exactly the same matched value, just also
  -- named).  Inner is elaborated first so its sub-binders are
  -- already in scope when we add @name@.  Duplicate-binder
  -- discipline (rejecting @name\@(Foo name)@ shadows or
  -- repeated names across siblings) lives in a separate lint
  -- carrier, not here.
  valAt _ann name _binderPath inner = HypTwr $ \env -> do
    (innerVal, env1) <- runHypTwr inner env
    let innerTower = sValTower innerVal
        env2 = env1
          { hypTwrEnvValVars =
              Map.insert name innerTower (hypTwrEnvValVars env1) }
    Right (HypTwrSVal innerTower, env2)

  -- Value-level lambda: introduce a fresh metavariable for the
  -- binder's type, elaborate the body with that binder in scope,
  -- then build a 'TyArrV' tower from binder-type → body-type.  The
  -- binder's identity is its 'binderPath'; the meta uses the same
  -- path for both slots, matching the convention in 'valVar's
  -- Dissect-side binding logic.  The binder is removed from scope
  -- before returning so it doesn't leak.
  valLam _ann name binderPath body = HypTwr $ \env -> do
    let binderTower = leafTower env (TyMetaV (MetaId binderPath binderPath))
        savedVars   = hypTwrEnvValVars env
        envWithBind = env
          { hypTwrEnvValVars =
              Map.insert name binderTower (hypTwrEnvValVars env) }
    (bodyVal, env1) <- runHypTwr body envWithBind
    let bodyTower = sValTower bodyVal
        env2      = env1 { hypTwrEnvValVars = savedVars }
        lamView   = TyArrV (horizontal binderTower) (horizontal bodyTower)
        lamTower  = leafTower env2 lamView
    Right (HypTwrSVal lamTower, env2)

  -- Value-level application @f x@: elaborate both children, then
  -- meet @f@'s type against @Arr (typeof x) (fresh result meta)@.
  -- The successful meet refines the result meta (and any free metas
  -- in @f@'s type) to their unified shape; the result tower is the
  -- meta, which 'materialize' will resolve later.
  valApp _ann appPath f x = HypTwr $ \env -> do
    (fVal, env1) <- runHypTwr f env
    (xVal, env2) <- runHypTwr x env1
    let fTower       = sValTower fVal
        xTower       = sValTower xVal
        resultMeta   = leafTower env2 (TyMetaV (MetaId appPath appPath))
        expectedView = TyArrV (horizontal xTower) (horizontal resultMeta)
        expected     = hPure expectedView
    case meetNorm env2 (horizontal fTower) expected of
      Left e       -> Left e
      Right subst' ->
        let env3 = env2 { hypTwrEnvSubst = subst' }
        in Right (HypTwrSVal resultMeta, env3)
