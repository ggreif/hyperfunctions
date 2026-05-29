{-# LANGUAGE GADTs #-}

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
  , meet
  ) where

import Constructor.HyperLite (Hyper, hPure, hRun)
import Constructor.Level (Lv)
import Constructor.Path (Path)
import Constructor.Syntax (Name)
import Constructor.Tinf (TyErr (..))
import Constructor.TyExpr (TyExpr (..))

-- | One-layer unfolding of a type.  Children of compound shapes are
--   'TyProc's by recursion, so unfolding cost is paid lazily as the
--   web is traversed.
data TyView
  = TyConV  !Name !Path        -- ^ nullary type-constructor; identified by decl path
  | TyVarV  !Name !Path        -- ^ data-parameter reference; identified by binder path
  | TyAppV  !TyProc !TyProc    -- ^ type-level application
  | TyArrV  !TyProc !TyProc    -- ^ function type
  | TyUnivV !Lv                -- ^ universe at a level
  | TyMetaV !Path !Path        -- ^ fresh metavariable; @(def-path, use-path)@
                               --   identity.  Inert in commit 4 — present
                               --   so a later commit's unifier doesn't
                               --   reshape the algebra.

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
    oneLayer (TyCon n p) = TyConV n p
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
viewToTy (TyConV n p)  = TyCon n p
viewToTy (TyVarV n pa) = TyVar n pa
viewToTy (TyAppV f x)  = TyApp (procToTy f) (procToTy x)
viewToTy (TyArrV a b)  = TyArr (procToTy a) (procToTy b)
viewToTy (TyUnivV l)   = TyUniv l
viewToTy (TyMetaV _ _) =
  error "Constructor.TyProc.viewToTy: unresolved metavariable \
        \(expected only after a later commit lands meta resolution)"

-- | Structural unification on type-processes.
--
--   For commit 5 this handles the *concrete-concrete* fragment of
--   Robinson unification: matching heads recurse into their children;
--   mismatched heads return 'TyMismatch'.  Metavariable resolution
--   (@TyMetaV@) is intentionally deferred — within a single data
--   declaration the parser already syntactically equates all uses of
--   the same binder via 'tyParamRef', so the algebra has no customer
--   for meta unification yet.  Once multi-site instantiation (commit
--   6+) introduces per-use fresh α-cells, 'meet' grows the redirect
--   case the design notes describe; the *encoding choice* — redirect
--   over constant, to preserve unification traces — is recorded in
--   PLAN.md, not enforced here.
--
--   The carrier itself (`HypTinf`) does not yet invoke 'meet' — there
--   is no expression-level grammar feature whose well-formedness
--   forces unification.  This module ships the apparatus; the
--   customer lands in a later commit.
meet :: TyProc -> TyProc -> Either TyErr TyProc
meet p1 p2 = hPure <$> meetView (hRun p1) (hRun p2)
  where
    meetView v1 v2 = case (v1, v2) of
      (TyConV n1 p1', TyConV n2 p2')
        | n1 == n2 && p1' == p2' -> Right v1
      (TyVarV n1 p1', TyVarV n2 p2')
        | n1 == n2 && p1' == p2' -> Right v1
      (TyAppV f1 x1, TyAppV f2 x2) -> do
        f3 <- meet f1 f2
        x3 <- meet x1 x2
        Right (TyAppV f3 x3)
      (TyArrV a1 b1, TyArrV a2 b2) -> do
        a3 <- meet a1 a2
        b3 <- meet b1 b2
        Right (TyArrV a3 b3)
      (TyUnivV l1, TyUnivV l2)
        | l1 == l2 -> Right v1
      (TyMetaV _ _, _) ->
        error "Constructor.TyProc.meet: metavariable unification \
              \deferred to a later commit"
      (_, TyMetaV _ _) ->
        error "Constructor.TyProc.meet: metavariable unification \
              \deferred to a later commit"
      _ -> Left (TyMismatch (viewToTy v1) (viewToTy v2))
