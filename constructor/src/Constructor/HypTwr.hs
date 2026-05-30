{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

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
  , hypTwrCtorTypes
  , CtorSig (..)
  , extractCtorSig
  ) where

import Constructor.HyperLite (hPure, hRun)
import Constructor.Level (Lv (..), starLevel)
import Constructor.Path (Path, PathStep (..), emptyPath, extendPath)
import Constructor.Sort (Sort (..))
import Constructor.Syntax (Lang (..), Name)
import Constructor.Tinf (TyErr (..))
import Constructor.Tower
  ( Tower (..)
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
import Data.Kind (Type)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

-- | Per-sort carrier value.  'SExpr' carries a 'Tower' directly; the
--   ctor decl slot pairs the ctor's name with its tower; the data
--   decl slot is 'Nothing' (matching 'HypTinf').  Value-level and
--   arm carriers now also carry 'Tower' payloads: in 'Build' mode
--   the tower is the expression's inferred type; in 'Dissect' mode
--   it's a placeholder (a fresh meta) — Dissect-side typing lands
--   in the next sub-commit, which will replace the placeholder with
--   the pattern's actual type as derived from the scrutinee.
data HypTwrVal (s :: Sort) where
  HypTwrExpr  :: !Tower                       -> HypTwrVal 'SExpr
  HypTwrDecl  :: !(Maybe (Name, Tower))       -> HypTwrVal 'SDecl
  HypTwrProg  ::                                  HypTwrVal 'SProg
  HypTwrSVal  :: !Tower                       -> HypTwrVal ('SVal m)
  HypTwrSArm  :: !Tower                       -> HypTwrVal 'SArm

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
  , hypTwrEnvMode      :: !ElabMode
    -- ^ Runtime mode: 'ElabBuild' (the default) flips to
    --   'ElabDissect' while elaborating an arm's pattern, and
    --   back to 'ElabBuild' for its body.  Read by 'valVar' to
    --   decide whether a name introduces a binder or resolves a
    --   reference.
  }

emptyHypTwrEnv :: HypTwrEnv
emptyHypTwrEnv = HypTwrEnv Map.empty Map.empty Map.empty emptySubst Nothing
                            Map.empty ElabBuild

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
hypTwrProgram p = do
  (_, env) <- runHypTwr p emptyHypTwrEnv
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

-- | Walk a list of arms, collect each arm's body tower (used by
--   'case_' to pairwise-meet body types).  Each arm internally
--   restores the env's val-binders to the outer scope, so the
--   accumulator only grows with the threaded 'Subst'.
threadArmBodies
  :: [HypTwr a 'SArm] -> HypTwrEnv -> Either TyErr ([Tower], HypTwrEnv)
threadArmBodies []     env = Right ([], env)
threadArmBodies (a:as) env = do
  (armVal, env1) <- runHypTwr a env
  let bodyTower = sArmTower armVal
  (rest, env2) <- threadArmBodies as env1
  pure (bodyTower : rest, env2)

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

-- | Extract the body tower from an arm carrier.
sArmTower :: HypTwrVal 'SArm -> Tower
sArmTower (HypTwrSArm t) = t

-- | Build a "Parent applied to fresh metas" tower for a ctor's
--   Build-side use site.  One meta per parent parameter (binder
--   path = the parameter's def-slot inside the parent, use path =
--   the ctor's call site).  For a nullary parent (arity 0) the
--   result is just the parent's 'TyConV' — no application chain.
--
--   This is /not/ the eventually-correct result type (which would
--   substitute the parent's TyVarVs throughout 'CtorSig.refinements'
--   with these fresh metas); it's a /shape-compatible/ placeholder
--   that lets arm bodies meet pairwise through metavariable
--   binding while the refinement-walking machinery is still ahead
--   of us.  When that lands, this helper grows to consume
--   'ctorRefinements' directly.
mkCtorResultTower
  :: HypTwrEnv -> Name -> Path -> Int -> Path -> Tower
mkCtorResultTower env parentName parentPath arity callPath =
  leafTower env (chain (TyConV parentName parentPath Z) 0)
  where
    chain hView i
      | i >= arity = hView
      | otherwise  =
          let metaProc = mkMeta (extendPath (PsDataParam i) parentPath) callPath
              hProc    = hPure hView
          in chain (TyAppV hProc metaProc) (i + 1)

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

  -- Parser owns tycon resolution; bare 'var' is only reached for
  -- genuinely unbound names.
  var _ann n = HypTwr $ \_env -> Left (TyUnbound n)

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

  valDecl _ann _declPath name body = HypTwr $ \env ->
    case Map.lookup name (hypTwrEnvValVars env) of
      Just _  -> Left (TyDuplicateCtor name)
      Nothing -> do
        (bodyVal, env1) <- runHypTwr body env
        let bodyTower = sValTower bodyVal
            env2 = env1
              { hypTwrEnvValVars =
                  Map.insert name bodyTower (hypTwrEnvValVars env1) }
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

  valCtor _ann name callPath args = HypTwr $ \env -> case hypTwrEnvMode env of
    ElabBuild -> do
      ctorTower <- maybe (Left (TyUnbound name)) Right
                     (Map.lookup name (hypTwrEnvCtors env))
      let subst              = hypTwrEnvSubst env
          (_, headView, _)   = peelCtorTower subst ctorTower
      case (extractCtorSig subst ctorTower, headView) of
        (Just sig, TyConV pName pPath _)
          | length args /= length (ctorInputs sig) ->
              Left (TyCtorWrongArity name pName
                     (length (ctorInputs sig)) (length args))
          | otherwise -> do
              -- Walk args in Build mode; per-arg meet against
              -- ctorInputs is deferred until the substitution
              -- walk lands (next sub-commit).
              env' <- threadVals args env
              let arity = maybe 0 id (Map.lookup pName (hypTwrEnvDataTypes env'))
                  resultTower = mkCtorResultTower env' pName pPath arity callPath
              Right (HypTwrSVal resultTower, env')
        _ -> Left (TyCtorBadResult name)
    ElabDissect ->
      case Map.lookup name (hypTwrEnvCtors env) of
        Nothing -> Left (TyUnbound name)
        Just _  -> do
          env' <- threadVals args env
          -- Placeholder result tower keyed on the ctor's call
          -- site; tightens to "Parent applied to refinement with
          -- skolems" in the next sub-commit.
          let placeholderTower =
                leafTower env' (TyMetaV (MetaId callPath callPath))
          Right (HypTwrSVal placeholderTower, env')

  case_ _ann scrutinee arms = HypTwr $ \env -> do
    (_, env1) <- runHypTwr scrutinee env
    -- Walk arms, collecting each body's tower.  Pattern binders
    -- introduced in each arm are restored at arm's exit
    -- (see 'arm' below), so the threaded env never accumulates
    -- per-arm bindings.
    (bodyTowers, env2) <- threadArmBodies arms env1
    -- All arm-body towers must unify (meet pairwise on the first
    -- rung).  The case as a whole types at the common tower.
    finalSubst <- meetAllTowers (hypTwrEnvSubst env2) bodyTowers
    let env3 = env2 { hypTwrEnvSubst = finalSubst }
        resultTower = case bodyTowers of
          (t:_) -> t
          []    -> leafTower env3 (TyMetaV (MetaId emptyPath emptyPath))
    Right (HypTwrSVal resultTower, env3)

  arm _ann pat body = HypTwr $ \env -> do
    let savedVars  = hypTwrEnvValVars env
        savedMode  = hypTwrEnvMode env
        envD       = env { hypTwrEnvMode = ElabDissect }
    (_, env1) <- runHypTwr pat envD
    let envB = env1 { hypTwrEnvMode = ElabBuild }
    (bodyVal, env2) <- runHypTwr body envB
    let bodyTower = sValTower bodyVal
        env3 = env2
          { hypTwrEnvValVars = savedVars
          , hypTwrEnvMode    = savedMode
          }
    Right (HypTwrSArm bodyTower, env3)
