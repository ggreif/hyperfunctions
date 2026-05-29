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
  ) where

import Constructor.HyperLite (Hyper, hPure, hRun)
import Constructor.Level (Lv)
import Constructor.Path (Path)
import Constructor.Syntax (Name)
import Constructor.TyExpr (TyExpr (..))

-- | One-layer unfolding of a type.  Children of compound shapes are
--   'TyProc's by recursion, so unfolding cost is paid lazily as the
--   web is traversed.
data TyView
  = TyConV  !Name              -- ^ nullary type-constructor reference
  | TyVarV  !Name !Path        -- ^ data-parameter reference (Stern-Gerlach path)
  | TyAppV  !TyProc !TyProc    -- ^ type-level application
  | TyArrV  !TyProc !TyProc    -- ^ function type
  | TyUnivV !Lv                -- ^ universe at a level
  | TyMetaV !Path !Path        -- ^ fresh metavariable; @(def-path, use-path)@
                               --   identity.  Inert in commit 4 — present
                               --   so commit 5's unifier doesn't reshape
                               --   the algebra.

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
    oneLayer (TyCon n)   = TyConV n
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
procToTy p = viewToTy (hRun p)
  where
    viewToTy (TyConV n)    = TyCon n
    viewToTy (TyVarV n pa) = TyVar n pa
    viewToTy (TyAppV f x)  = TyApp (procToTy f) (procToTy x)
    viewToTy (TyArrV a b)  = TyArr (procToTy a) (procToTy b)
    viewToTy (TyUnivV l)   = TyUniv l
    viewToTy (TyMetaV _ _) =
      error "Constructor.TyProc.procToTy: unresolved metavariable \
            \(expected only post-commit-5)"
