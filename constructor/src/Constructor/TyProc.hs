{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Type-processes for the B-side type-inference carrier.
--
--   A 'TyProc' is a hyperfunction valued in a one-layer-unfolded view
--   of the type ('TyView').  Children remain as 'TyProc's by
--   recursion, so the whole type is a *web* of hyperfunctions rather
--   than a syntactic tree — extraction happens by self-application
--   ('hRun'), not by pattern-matching a constructor.
--
--   This is the substrate for Architecture B's unification: each
--   place IS a hyperfunction, and identifications happen via
--   peer-callback negotiation rather than via union-find rewrites in
--   a side-substrate.  Commit 4 establishes the algebra and a
--   bijection with 'TyExpr' (via 'tyToProc' / 'procToTy'); the
--   genuine algebraic workout — metavariable unification with
--   path-tracing rewires — arrives in commit 5.
--
--   The 'TyMetaV' constructor of 'TyView' is the parking slot for
--   commit-5's fresh metavariables (addressed by their
--   (def-path, use-path) pair, à la Stern-Gerlach).  Commit 4 never
--   builds one; 'procToTy' errors if it sees one.
module Constructor.TyProc
  ( TyView (..)
  , TyProc
  , tyToProc
  , procToTy
  , viewToTy
  , viewToTySoft
    -- * Metavariables and unification
  , MetaId (..)
  , Subst
  , emptySubst
  , mkMeta
  , meet
  , occurs
  , materialize
  , resolveView
  ) where

import Constructor.HyperLite (Hyper, hPure, hRun)
import Constructor.Level (Lv (..))
import Constructor.Path (Path, emptyPath)
import Constructor.Syntax (Name)
import Constructor.Tinf (TyErr (..))
import Constructor.TyExpr (TyExpr (..))
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

-- | One-layer unfolding of a type.  Children of compound shapes are
--   'TyProc's by recursion, so unfolding cost is paid lazily as the
--   web is traversed.
data TyView
  = TyConV  !Name !Path !Lv    -- ^ nullary type-constructor; identified by decl
                               --   path.  The 'Lv' is a /deck-shift offset/ — the
                               --   covering-space level above the tycon's own
                               --   rung.  Surface uses always start at offset 'Z';
                               --   non-zero offsets arise from 'kindOf' on a
                               --   self-referential tycon (e.g. @data Weird :
                               --   Weird@'s upward tower bumps offset by one per
                               --   climb, giving productive codata rather than a
                               --   stationary stream).
  | TyVarV  !Name !Path        -- ^ data-parameter reference; identified by binder path
  | TyAppV  !TyProc !TyProc    -- ^ type-level application
  | TyArrV  !TyProc !TyProc    -- ^ function type
  | TyUnivV !Lv                -- ^ universe at a level
  | TyMetaV !MetaId            -- ^ fresh metavariable allocated at a parametric
                               --   tycon use-site.

-- | Identity of a metavariable allocated at a parametric tycon
--   use-site.  The first 'Path' is the parameter binder's def-path
--   (e.g. @[…List…, PsDataParam 0]@ for List's 0th parameter); the
--   second is the application path-as-a-whole (so two distinct
--   syntactic uses of @List Nat@ vs @List Bool@ produce metas with
--   distinct use-paths and hence distinct identities).
data MetaId = MetaId !Path !Path
  deriving (Eq, Ord, Show)

-- | A substitution from metavariables to their currently-bound
--   'TyView'.  Bound views may themselves mention other metas — the
--   redirect encoding from PLAN.md: lookups chase the chain through
--   'resolveSubst' / 'materialize'.  No @Map MetaId TyProc@ because
--   only the *one-layer view* a meta has settled on matters; further
--   resolution recurses.
type Subst = Map MetaId TyView

emptySubst :: Subst
emptySubst = Map.empty

-- | Construct a metavariable cell at the given @(binder, use)@ path
--   pair.  The cell is initially free — its identity is the
--   'MetaId'; whether it has been bound is consulted via 'Subst'.
mkMeta :: Path -> Path -> TyProc
mkMeta binderPath usePath = hPure (TyMetaV (MetaId binderPath usePath))

-- | A type-process: a hyperfunction that, when self-applied via
--   'hRun', yields its 'TyView'.  Identifications between two
--   processes happen by peer-callback negotiation (commit 5+); for
--   commit 4 every process is @hPure view@ for some statically-known
--   view.
type TyProc = Hyper TyView TyView

-- | Embed a 'TyExpr' as a 'TyProc' web.  Each compound constructor
--   becomes one layer of view with its children recursively embedded;
--   atoms become constant hyperfunctions ('hPure') at the
--   corresponding view.
tyToProc :: TyExpr -> TyProc
tyToProc = hPure . oneLayer
  where
    oneLayer (TyCon n p) = TyConV n p Z
    oneLayer (TyVar n p) = TyVarV n p
    oneLayer (TyApp f x) = TyAppV (tyToProc f) (tyToProc x)
    oneLayer (TyArr a b) = TyArrV (tyToProc a) (tyToProc b)
    oneLayer (TyUniv l)  = TyUnivV l

-- | Extract a 'TyExpr' from a 'TyProc' web by self-application.
--   This is the dual of 'tyToProc': the "probe" / final-coalgebra
--   unfolder, written here as a direct recursive descent rather than
--   as a hyperfunction-valued probe (the two are observationally
--   equivalent at commit-4 scope; the genuine probe-shape is needed
--   only once metavariable unification arrives and intermediate
--   states are observable from the algebra).
procToTy :: TyProc -> TyExpr
procToTy = viewToTy . hRun

-- | Project a 'TyView' to its syntactic 'TyExpr', recursing on
--   children via 'procToTy'.  Useful when handling a view directly
--   (e.g. in error reporting from 'meet') without going via 'hRun'.
viewToTy :: TyView -> TyExpr
viewToTy (TyConV n p _) = TyCon n p   -- offset elided in syntactic projection
viewToTy (TyVarV n pa) = TyVar n pa
viewToTy (TyAppV f x)  = TyApp (procToTy f) (procToTy x)
viewToTy (TyArrV a b)  = TyArr (procToTy a) (procToTy b)
viewToTy (TyUnivV l)   = TyUniv l
viewToTy (TyMetaV _)   =
  error "Constructor.TyProc.viewToTy: unresolved metavariable; \
        \use 'materialize' with the carrier's 'Subst' instead"

-- | 'Subst'-aware variant of 'viewToTy' used in error paths: chases
--   bindings through the substitution and renders any remaining
--   unresolved metavariable as a placeholder 'TyVar' so error
--   construction never crashes.  The placeholder name @"?meta"@ is
--   a sentinel — callers that want a hard fail can keep using
--   'viewToTy' on already-materialised inputs.
viewToTySoft :: Subst -> TyView -> TyExpr
viewToTySoft s v = case resolveView s v of
  TyConV n p _ -> TyCon n p
  TyVarV n pa  -> TyVar n pa
  TyAppV f x   -> TyApp (procToTySoft s f) (procToTySoft s x)
  TyArrV a b   -> TyArr (procToTySoft s a) (procToTySoft s b)
  TyUnivV l    -> TyUniv l
  TyMetaV _    -> TyVar "?meta" emptyPath

procToTySoft :: Subst -> TyProc -> TyExpr
procToTySoft s p = viewToTySoft s (hRun p)

-- | Resolve a 'TyView' against the current 'Subst': if it's a bound
--   metavariable, follow the redirect chain until a non-meta view or
--   an unbound meta surfaces.
resolveView :: Subst -> TyView -> TyView
resolveView s v0 = case v0 of
  TyMetaV mid
    | Just v <- Map.lookup mid s -> resolveView s v
  _ -> v0

-- | Structural unification on type-processes, threaded through a
--   'Subst' of metavariable bindings.
--
--   * Concrete ≡ concrete: matching heads recurse into their
--     children; mismatched heads return 'TyMismatch'.
--   * Meta ≡ anything: extends 'Subst' with the binding @meta := v@.
--     The redirect encoding from PLAN.md: the bound view may
--     itself mention other metas; 'meet' does not eagerly resolve
--     the chain.  Subsequent 'materialize' (or recursive 'meet')
--     chases through.
--   * Meta ≡ same meta: no-op (the binding is already implicit).
--
--   Structural occurs check: before binding @m := v@, refuses if @v@
--   transitively (via 'Subst' chasing and recursion into 'TyAppV' /
--   'TyArrV' children) contains @m@.  Without this guard,
--   'materialize' would loop on the cyclic substitution.
meet :: Subst -> TyProc -> TyProc -> Either TyErr Subst
meet s p1 p2 = meetView s (resolveView s (hRun p1)) (resolveView s (hRun p2))
  where
    meetView s' v1 v2 = case (v1, v2) of
      (TyMetaV m1, TyMetaV m2)
        | m1 == m2  -> Right s'
        | otherwise -> Right (Map.insert m1 (TyMetaV m2) s')
      (TyMetaV m, v) -> bind s' m v
      (v, TyMetaV m) -> bind s' m v
      (TyConV n1 p1' o1, TyConV n2 p2' o2)
        | n1 == n2 && p1' == p2' && o1 == o2 -> Right s'
      (TyVarV n1 p1', TyVarV n2 p2')
        | n1 == n2 && p1' == p2' -> Right s'
      (TyAppV f1 x1, TyAppV f2 x2) -> do
        s1 <- meet s' f1 f2
        meet s1 x1 x2
      (TyArrV a1 b1, TyArrV a2 b2) -> do
        s1 <- meet s' a1 a2
        meet s1 b1 b2
      (TyUnivV l1, TyUnivV l2)
        | l1 == l2 -> Right s'
      _ -> Left (TyMismatch (viewToTySoft s' v1) (viewToTySoft s' v2))

    bind s' m@(MetaId bp up) v
      | occurs s' m v = Left (TyOccursCheck bp up)
      | otherwise     = Right (Map.insert m v s')

-- | Structural occurs check: does 'MetaId' @m@ appear anywhere in @v@
--   (or transitively through 'Subst' chasing and recursion into
--   'TyAppV' / 'TyArrV' children)?  The standard Robinson guard.
occurs :: Subst -> MetaId -> TyView -> Bool
occurs s m v0 = case resolveView s v0 of
  TyMetaV m'  -> m == m'
  TyAppV f x  -> occurs s m (hRun f) || occurs s m (hRun x)
  TyArrV a b  -> occurs s m (hRun a) || occurs s m (hRun b)
  TyConV{}    -> False
  TyVarV{}    -> False
  TyUnivV{}   -> False

-- | Walk a 'TyProc' web under a 'Subst', producing a syntactic
--   'TyExpr'.  Bound metavariables are followed through the
--   substitution; unbound metavariables produce 'TyUnresolvedMeta'.
materialize :: Subst -> TyProc -> Either TyErr TyExpr
materialize s p = materializeView (resolveView s (hRun p))
  where
    materializeView (TyConV n pa _) = Right (TyCon n pa)   -- offset elided
    materializeView (TyVarV n pa) = Right (TyVar n pa)
    materializeView (TyAppV f x)  = TyApp <$> materialize s f <*> materialize s x
    materializeView (TyArrV a b)  = TyArr <$> materialize s a <*> materialize s b
    materializeView (TyUnivV l)   = Right (TyUniv l)
    materializeView (TyMetaV (MetaId bp up)) = Left (TyUnresolvedMeta bp up)
