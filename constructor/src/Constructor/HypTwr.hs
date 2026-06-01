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
  , hypTwrCtorTypes
  , CtorSig (..)
  , extractCtorSig
  ) where

import Constructor.HyperLite (hPure, hRun)
import Constructor.Interp (Globals, narrowOnce, normaliseDeferred)
import Constructor.Level (Lv (..), starLevel)
import Control.Applicative (empty)
import Control.Monad.Logic (Logic, ifte, observeMany)
import Constructor.Path (Path, emptyPath)
import Constructor.Sort (Sort (..))
import Constructor.Syntax (Lang (..), Name)
import Constructor.Tinf (TyErr (..))
import Constructor.Tower
  ( Tower
  , Gamma (..)
  , kindOf
  , meetTowers
  , towerOfView
  , horizontalView
  )
import Constructor.TyExpr (TyExpr)
import Constructor.TyProc
  ( MetaId (..)
  , Subst
  , TyProc
  , TyView (..)
  , emptySubst
  , eqView
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
  -- ^ Arm carrier: 'Nothing' = unreachable (pattern clashed with
  --   scrutinee); 'Just (bakedTower, armSubst)' for reachable arms,
  --   where 'armSubst' is the post-body arm-local 'Subst' before
  --   any per-arm restoration.  'case_' intersects arm Substs at
  --   exit (entries agreed by all reachable arms propagate; per-arm
  --   pattern-binder metas and conflicting outer-meta refinements
  --   drop) — see note on commit 0aa6e9d for the design.
  HypTwrSArm  :: !(Maybe (Tower, Subst))      -> HypTwrVal 'SArm

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
                            Map.empty Map.empty Map.empty Map.empty
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
--   callers that want demote-interpret-promote bridging plus Phase-D
--   narrowing for 'TyDeferV' applications.  When both maps are empty,
--   behaves identically to 'hypTwrProgram' (no reductions fire
--   because 'normaliseDeferred' / 'narrowOnce' have nothing to look
--   up).  Narrowing reads candidate ctors from each deferred
--   function's own @case@ arms (via 'Globals'), so no per-data ctor
--   table is threaded.
hypTwrProgramWith
  :: Globals -> Map Name Path -> HypTwr a 'SProg -> Either TyErr HypTwrResult
hypTwrProgramWith gs cps p = do
  let env0 = emptyHypTwrEnv
        { hypTwrEnvGlobals   = gs
        , hypTwrEnvCtorPaths = cps
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

-- | Deep-resolve a 'TyView' under a 'Subst', threading
--   'resolveView' through 'TyAppV' / 'TyArrV' children so that
--   bindings at any depth are inlined into the returned view.
--
--   Used by the per-arm Subst-fork at 'arm' exit: an arm's body
--   tower has its meta references baked against the arm-local
--   Subst, so that pattern-binder refinements (e.g. @?m := S Z@
--   from a 'FS m' pattern against a 'Fin 2' scrutinee) survive the
--   subsequent drop of the arm-local Subst.  Outer-meta refinements
--   (the lambda-binder's @?xs := List a Z@ in the polymorphic-
--   scrutinee case) are typically not referenced by the body tower
--   and so are harmlessly forgotten — exactly what the "arm as
--   function" framing prescribes.
deepResolveView :: Subst -> TyView -> TyView
deepResolveView s v = case resolveView s v of
  TyAppV f x -> TyAppV (deepResolveProc s f) (deepResolveProc s x)
  TyArrV a b -> TyArrV (deepResolveProc s a) (deepResolveProc s b)
  TyCaseV scrut arms ->
    TyCaseV (deepResolveView s scrut)
            [(deepResolveView s p, deepResolveView s b) | (p, b) <- arms]
  other      -> other

deepResolveProc :: Subst -> TyProc -> TyProc
deepResolveProc s p = hPure (deepResolveView s (hRun p))

-- | Intersect per-arm 'Subst' diffs against a common parent: keep
--   only entries that all reachable arms agree on (same key, same
--   value modulo 'eqView') AND whose key isn't already bound in the
--   parent.  Empty arm-list yields the empty diff (case-of with no
--   reachable arms doesn't refine outer scope).
intersectArmDiffs :: Subst -> [Subst] -> Subst
intersectArmDiffs _      []       = Map.empty
intersectArmDiffs parent (s : ss) =
  let diff0 = Map.difference s parent
      meet a b = Map.mapMaybeWithKey
                   (\k v -> case Map.lookup k b of
                              Just v' | eqView v v' -> Just v
                              _                     -> Nothing)
                   a
  in foldr meet diff0 (map (`Map.difference` parent) ss)

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
           -- R4 of v0.5.0 (.claude/plans/lvannot-shape.md): iso-tower
           -- singleton ctor whose result head is the CTOR itself
           -- ('Cons : ∀x y. x → y → Cons x y' shape from buildCtorSugar).
           -- This is the covering-space form for parametric iso-tower
           -- data; the parent's covering-space relationship is
           -- structural (ctor singletons collectively cover the parent
           -- type), not a head-identity match.
           | h == ctorName    -> Right ()
           | otherwise        -> Left (TyCtorWrongHead ctorName parentName h)
         _ -> Left (TyCtorBadResult ctorName)

-- | Elaborate a single data-parameter's kind expression (if present)
--   for its side-effect of allocating a kind-meta in HypTwr's
--   machinery.  The resulting tower is discarded — the meta lives
--   on via its 'MetaId' allocation path, accessible at use sites
--   via the parser-determined path.  R3 (v0.5.0) — see
--   '.claude/plans/lvannot-shape.md'.
elabParamKind :: HypTwrEnv -> (Name, Maybe (HypTwr a 'SExpr)) -> Either TyErr HypTwrEnv
elabParamKind env (_n, Nothing)        = Right env
elabParamKind env (_n, Just kindExpr)  = do
  (_, env') <- runHypTwr kindExpr env
  pure env'

-- | Is a 'kindOf' result concrete enough to bind a kind-meta to it?
--   Used by 'app's R3c use-site resolution rule.  Self-referential
--   ('TyConV' iso-tower) and classical ('TyUnivV') both qualify;
--   unresolved metas and deferred chains don't.
isKindMetaResolvable :: TyView -> Bool
isKindMetaResolvable v = case v of
  TyConV{}  -> True
  TyAppV{}  -> True
  TyUnivV{} -> True
  _         -> False

threadDecls :: [HypTwr a 'SDecl] -> HypTwrEnv -> Either TyErr HypTwrEnv
threadDecls []     env = Right env
threadDecls (d:ds) env = do
  (_, env1) <- runHypTwr d env
  threadDecls ds env1

-- | Walk a list of arms, collecting each arm's @Maybe Tower@
--   reachability marker (used by 'case_' to filter to reachable
--   bodies and pairwise-meet their towers).  Each arm internally
--   restores the env's val-binders to the outer scope, so the
--   accumulator only grows with the threaded 'Subst'.
threadArmsCarrying
  :: [HypTwr a 'SArm] -> HypTwrEnv -> Either TyErr ([Maybe (Tower, Subst)], HypTwrEnv)
threadArmsCarrying []     env = Right ([], env)
threadArmsCarrying (a:as) env = do
  (armVal, env1) <- runHypTwr a env
  let armRes = case armVal of HypTwrSArm m -> m
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
      kEnv    = hypTwrEnvKindEnv env
      v1      = normaliseDeferred gs cps kEnv s (hRun p1)
      v2      = normaliseDeferred gs cps kEnv s (hRun p2)
  in case meet s (hPure v1) (hPure v2) of
       Right s' -> Right s'
       Left err ->
         -- Phase D: try narrowing on either side's TyDeferV chain.
         -- The candidate search is a 'Logic' stream; 'observeMany 1'
         -- takes the first refinement whose meet succeeds (plain
         -- '>>=' keeps DFS order, so this matches the previous
         -- list-based first-wins behaviour).
         let cands1 = candidatesFor gs cps kEnv s v1
             cands2 = candidatesFor gs cps kEnv s v2
             search = do
               (sub1, v1') <- cands1
               (sub2, v2') <- cands2
               let s'' = sub2 `Map.union` sub1 `Map.union` s
               case meet s'' (hPure v1') (hPure v2') of
                 Right s' -> pure s'
                 Left _   -> empty
         in case observeMany 1 search of
              (s' : _) -> Right s'
              []       -> Left err
  where
    -- | Narrowing candidates for a single TyView, with recursion
    --   into children.  For a TyAppV chain rooted at TyDeferV,
    --   return the narrow-once enumeration; otherwise recurse
    --   into TyAppV / TyArrV children so nested deferred-chains
    --   (e.g., the @pickZ ?n@ inside @Eq Z (pickZ ?n)@) surface.
    candidatesFor :: Globals -> Map Name Path -> Map Name TyProc
                  -> Subst -> TyView -> Logic (Subst, TyView)
    candidatesFor gs cps kEnv s v = case resolveView s v of
      TyAppV f x ->
        case peelDeferredHead s (TyAppV f x) of
          -- Narrow if 'narrowOnce' offers anything; else fall back to
          -- the un-narrowed view ('ifte' = soft cut: run the fallback
          -- only when the stream is empty).
          Just (fname, argViews) ->
            ifte (narrowOnce gs cps kEnv s fname argViews)
                 pure
                 (pure (Map.empty, TyAppV f x))
          Nothing ->
            -- Not deferred at this level — recurse into children
            -- so a nested deferred-chain can still be discovered.
            do (sf, vf) <- candidatesFor gs cps kEnv s (hRun f)
               (sx, vx) <- candidatesFor gs cps kEnv s (hRun x)
               pure (sf `Map.union` sx, TyAppV (hPure vf) (hPure vx))
      TyArrV a b ->
        do (sa, va) <- candidatesFor gs cps kEnv s (hRun a)
           (sb, vb) <- candidatesFor gs cps kEnv s (hRun b)
           pure (sa `Map.union` sb, TyArrV (hPure va) (hPure vb))
      other -> pure (Map.empty, other)

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
  TyCaseV scrut arms ->
    TyCaseV (substTyVarsInView m scrut)
            [(substTyVarsInView m p, substTyVarsInView m b) | (p, b) <- arms]

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
        -- R3 (v0.5.0): elaborate each param's kind expression so
        -- kind metas (emitted by 'collectParams' via Phase 1)
        -- reach HypTwr's machinery.  We discard the resulting
        -- tower; the meta is allocated through the leaf-tower's
        -- 'TyMetaV' (via R1's 'tyKindMeta' override) and persists
        -- via its 'MetaId'.  Use-site resolution (R3 follow-on)
        -- meets these against actual arg kinds at ctor application
        -- sites.
        envInit <- foldM elabParamKind env params
        (eVal, env0) <- runHypTwr e envInit
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
        -- R2 of v0.5.0 (.claude/plans/lvannot-shape.md): register
        -- the ctor's RESULT type (one rung up) in 'kindEnv' so
        -- 'kindOf' on a ctor application gives its kind.  For
        -- iso-tower-singleton ctors ('Cons : ∀x y. x → y → Cons x y'),
        -- the result-view is the ctor's own head (self-applied form
        -- when parametric), so 'kindOf' triggers Phase 2's
        -- parametric self-loop — propagating iso-tower-ness through
        -- the kind dimension.  For classical ctors ('mkFoo : Foo'),
        -- the result-view is the parent's head, so 'kindOf'
        -- walks up to the parent's kind.
        let subst                   = hypTwrEnvSubst env1
            (_, ctorHead, ctorRefs) = peelCtorTower subst tower
            ctorKindView            = mkAppChainView ctorHead ctorRefs
            ctorKindProc            = hPure ctorKindView
            env2 = env1
              { hypTwrEnvCtors   = Map.insert name tower (hypTwrEnvCtors env1)
              , hypTwrEnvKindEnv =
                  Map.insert name ctorKindProc (hypTwrEnvKindEnv env1)
              }
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
  -- (option-β's horizontal layer stores TyProcs, not Towers).
  --
  -- R3c (v0.5.0): if f's kindOf is an unresolved kind-meta and x's
  -- kindOf is concrete, bind the meta to x's kind.  This is the
  -- use-site resolution rule from .claude/plans/lvannot-shape.md —
  -- 'List Bool' resolves List's kind-meta to '*0', 'List Bool⋮'
  -- resolves it to 'Bool' (self-ref).  Locks on first use (subsequent
  -- uses with conflicting arg kinds will TyMismatch — that's the
  -- correct conservative behaviour pending a more nuanced
  -- per-use freshening pass).
  app _ann _appPath f x = HypTwr $ \env -> do
    (vf, env1) <- runHypTwr f env
    (vx, env2) <- runHypTwr x env1
    let fProc = horizontal (exprTower vf)
        xProc = horizontal (exprTower vx)
        s     = hypTwrEnvSubst env2
        kEnv  = hypTwrEnvKindEnv env2
        fKind = kindOf s kEnv (hRun fProc)
        xKind = kindOf s kEnv (hRun xProc)
    env3 <- case fKind of
      TyMetaV m | isKindMetaResolvable xKind ->
        case Map.lookup m s of
          Nothing -> Right env2 { hypTwrEnvSubst = Map.insert m xKind s }
          Just _  -> Right env2  -- already bound; skip
      _ -> Right env2
    let tower = leafTower env3 (TyAppV fProc xProc)
    pure (HypTwrExpr tower, env3)

  forallLv _ann _name _binderPath body = HypTwr $ runHypTwr body
  existsTy _ann _name _binderPath body = HypTwr $ runHypTwr body

  starVar _ann _name _binderPath _offset = HypTwr $ \env ->
    Right (HypTwrExpr (leafTower env (TyUnivV Z)), env)

  -- R1 of v0.5.0 (.claude/plans/lvannot-shape.md): emit a 'TyMetaV'
  -- at the kind-meta's allocation path so the meta participates in
  -- 'Subst' alongside type metas.  Unification at use sites refines
  -- it: sticky args (TyUnivV) leave it unresolved (defaulting to
  -- '*0' at end-of-elaboration via R3 work); iso-tower args bind
  -- it to a self-referential 'TyConV' shape.
  --
  -- Both 'MetaId' paths set to the kind-meta's allocation path —
  -- there's no separate "use site" at allocation time; use-site
  -- distinctness comes from the freshly-emitted 'tyKindMeta' calls
  -- in 'collectParams' (each param gets a different 'PsDataParamKind
  -- i' path) and 'haskellStyleBody' ('PsDataAnn').
  tyKindMeta _ann path = HypTwr $ \env ->
    Right (HypTwrExpr (leafTower env (TyMetaV (MetaId path path))), env)

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
        reachableP = [(t, s) | Just (t, s) <- armResults]
        reachable  = map fst reachableP
        armSubsts  = map snd reachableP
    -- Intersect arm-local Substs over outer-meta bindings: keep
    -- only entries agreed-upon by all reachable arms (the "all arms
    -- agree" lattice rule from the design note).  For a 1-arm case
    -- this is trivially the arm's full diff; for multi-arm cases
    -- with conflicting refinements of an outer meta (e.g. Nil-arm
    -- '?xs := List a Z' vs Cons-arm '?xs := List a (S n)' in
    -- polymorphic-scrutinee 'case xs { Nil -> ...; Cons _ _ -> ...
    -- }'), the disagreement drops the binding so siblings/outer
    -- scope don't get poisoned.
    let baseSubst  = hypTwrEnvSubst env3
        agreedDiff = intersectArmDiffs baseSubst armSubsts
        mergedSubst = Map.union agreedDiff baseSubst
    -- Try pairwise-meeting the reachable arms' body towers.  When
    -- they agree (parametric ADT case-of, single reachable arm, etc.)
    -- the case-of has a single concrete result type.  When they
    -- DIVERGE *and* the scrutinee is still polymorphic (a meta), fall
    -- back to a TyCaseV: a deferred refinement-indexed family
    -- '(scrutBinding, bodyType)' per arm.  At meet sites, the
    -- TyCaseV reduces by picking the unique firing arm given the
    -- scrutinee's then-current resolution.
    --
    -- Heterogeneous arms over a CONCRETE scrutinee (e.g. 'case T
    -- { T -> T; F -> Z }' with Bool's 'T' and Nat's 'Z' arms) stay
    -- a genuine type error — TyCaseV's reduction can't disambiguate
    -- without indexed family structure, and there's no polymorphism
    -- to defer.
    let scrutView   = resolveView mergedSubst (horizontalView scrutTower)
        scrutIsPoly = case scrutView of
          TyMetaV{} -> True
          _         -> False
        armBindings =
          [ ( resolveView armSubst (horizontalView scrutTower)
            , horizontalView body)
          | (body, armSubst) <- reachableP ]
    case meetAllTowers mergedSubst reachable of
      Right finalSubst ->
        let env4 = env3 { hypTwrEnvSubst = finalSubst }
            resultTower = case reachable of
              (t:_) -> t
              []    -> leafTower env4
                         (TyMetaV (MetaId emptyPath emptyPath))
        in Right (HypTwrSVal resultTower, env4)
      Left err
        | scrutIsPoly ->
            let env4 = env3 { hypTwrEnvSubst = mergedSubst }
                caseView = TyCaseV scrutView armBindings
                caseTower = leafTower env4 caseView
            in Right (HypTwrSVal caseTower, env4)
        | otherwise -> Left err

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
              -- (Nothing, no arm-local Subst to ship; outer code
              -- treats this arm as not contributing to the
              -- intersection.)
          Right subst' -> do
            -- Reachable arm: elaborate the body under the arm-local
            -- Subst, bake refinements into the body tower, then
            -- drop arm-local refinements on exit (per-arm Subst-
            -- fork).  Sibling arms thus see the pre-arm Subst —
            -- their own pattern-side meets refine the scrutinee
            -- meta independently, so the Nil arm's '?α := List a Z'
            -- no longer poisons the Cons arm's '?α := List a (S n)'.
            -- Baking via 'deepResolveView' inlines pattern-binder
            -- refinements (e.g. '?m := S Z' from 'FS m' against
            -- 'Fin 2') into the body tower so they survive the
            -- Subst drop; outer-meta refinements are typically not
            -- referenced by the body tower and are harmlessly
            -- forgotten.  See note on this commit's ancestor for
            -- the "arm as function" framing.
            let env1' = env1
                  { hypTwrEnvSubst = subst'
                  , hypTwrEnvMode  = ElabBuild
                  }
            (bodyVal, env2) <- runHypTwr body env1'
            let bodyTower = sValTower bodyVal
                -- Bake under the FULL post-body Subst (not just the
                -- pattern-meet Subst), so refinements the body
                -- elaboration added — e.g. instantiating FS's 'n'
                -- to 'Z' inside 'FS m : Fin (S n)' — also survive
                -- the drop.
                bakedView = deepResolveView (hypTwrEnvSubst env2)
                                            (horizontalView bodyTower)
                bakedTower = towerOfView (hypTwrEnvSubst env)
                                         (hypTwrEnvKindEnv env2)
                                         bakedView
                env3 = env2
                  { hypTwrEnvValVars = savedVars
                  , hypTwrEnvMode    = savedMode
                  , hypTwrEnvSubst   = hypTwrEnvSubst env  -- pre-pat
                  }
            Right (HypTwrSArm (Just (bakedTower, hypTwrEnvSubst env2)), env3)

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
