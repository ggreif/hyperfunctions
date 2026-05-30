-- | Typing-tower codata (option β from PLAN.md).  Each 'Tower'
--   carries the horizontal 'TyView' at its current rung plus the
--   /lazy/ Tower one rung above — type, kind, super-kind, … as a
--   coinductively-defined stream.
--
--   Commit 7 (this module): scaffold only.  We define 'Tower', a
--   'liftTower' that takes the level the carrier value lives at and
--   produces a Tower whose vertical is the universe stream starting
--   one rung above, and a projection back to 'TyExpr' for the
--   parity check.  No carrier integration yet — 'HypTinf' continues
--   to emit 'TyProc'.  The subsequent commits in the Tower arc add:
--   the coalgebraic @infer@ step (kind/super-kind unfold), a
--   tower-aware 'meet' with the occurs check folded in, and a
--   'HypTwr' carrier emitting Towers directly.
--
--   The two slots have deliberately different algebraic properties
--   (PLAN.md's three-axis deck-group reading):
--
--   * 'horizontal' carries the groupoid-flavoured parametric content
--     — subject to symmetric 'meet' / metavariable inversion in
--     later commits.
--
--   * 'vertical' carries the directed @:@-step.  Codata; never
--     inverted; later commits add asymmetric (subtyping-flavoured)
--     unification along this axis.
--
--   For the scaffold the slots are independent; the algebraic
--   distinction starts paying off when commits 8+ add the
--   tower-aware operations.
module Constructor.Tower
  ( Tower (..)
  , liftTower
  , universeStream
  , climb
  , projectFirstRung
  ) where

import Constructor.HyperLite (hRun)
import Constructor.Level (Lv (..))
import Constructor.TyExpr (TyExpr)
import Constructor.TyProc (TyProc, TyView (..), viewToTy)

-- | A Tower is its horizontal 'TyView' at the current rung paired
--   with the (lazily-evaluated) Tower one rung above.  The vertical
--   slot is intentionally lazy — this is codata, finite generators
--   yielding potentially-infinite unfoldings.
data Tower = Tower
  { horizontal :: !TyView
  , vertical   :: Tower
  }

-- | Lift a 'TyProc' to a Tower at a given starting level.  The
--   horizontal is the proc's TyView; the vertical is the universe
--   stream starting one rung above.
--
--   The starting 'Lv' must be supplied by the caller because
--   'TyProc' doesn't yet carry per-node level info.  A later commit
--   in the Tower arc folds level inference and type elaboration into
--   one carrier, eliminating this argument; for the scaffold it's
--   left explicit.
liftTower :: Lv -> TyProc -> Tower
liftTower lv p = Tower
  { horizontal = hRun p
  , vertical   = universeStream (S lv)
  }

-- | The Tower whose every rung is the universe at the current level,
--   ascending forever.  Productive codata: the generator
--   @universeStream@ is finite, the unfolding is infinite.  Models
--   the stable tail of any non-polymorphic typing tower.
universeStream :: Lv -> Tower
universeStream lv = Tower
  { horizontal = TyUnivV lv
  , vertical   = universeStream (S lv)
  }

-- | One step up the tower (the directed @:@-arrow).  Total but
--   irreversible — there is no inverse function @descend@ because
--   the @:^{-1}@ relation is many-to-one over all preimages.
climb :: Tower -> Tower
climb = vertical

-- | Project the first rung's horizontal view back to a 'TyExpr'.
--   For a Tower lifted from a metavariable-free 'TyProc', this is
--   the parity invariant against today's 'procToTy':
--
--   @
--   projectFirstRung (liftTower lv p)  ==  procToTy p
--   @
projectFirstRung :: Tower -> TyExpr
projectFirstRung = viewToTy . horizontal
