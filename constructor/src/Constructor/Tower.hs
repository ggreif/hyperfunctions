-- | Typing-tower codata (option β from PLAN.md).  Each 'Tower'
--   carries the horizontal 'TyView' at its current rung plus the
--   /lazy/ Tower one rung above — type, kind, super-kind, … as a
--   coinductively-defined stream.
--
--   Commit 8 (this revision): the vertical is no longer a synthetic
--   universe stream supplied by the caller's 'Lv'; it is generated
--   by 'kindOf', the coalgebraic one-rung-up unfold.  Given a
--   'KindEnv' (built from declared @data … : K@ kind annotations by
--   'HypTinf'), 'kindOf' returns the next rung's horizontal view.
--   Repeated application produces the full upward tower
--   coinductively.
--
--   The vertical reaches a stable @*n@-stream tail once horizontal
--   structure has been exhausted — the @x^0 = 1@ collapse from the
--   memory file's covering-space framing.  For non-polymorphic
--   inputs the tail is observably a pure 'Lv'-successor codata; for
--   universe-polymorphic inputs it remains parametric in the level
--   variable.
--
--   The two algebraic axes per PLAN.md option (β):
--
--   * 'horizontal' carries the groupoid-flavoured parametric content
--     — subject to symmetric 'meet' / metavariable inversion.
--
--   * 'vertical' carries the directed @:@-step.  Codata, never
--     inverted; the eventual tower-aware 'meet' (Tower arc step 3)
--     will perform asymmetric subtyping-flavoured unification along
--     this axis with the @*n@-stable-tail termination condition.
module Constructor.Tower
  ( Tower (..)
    -- * Kind environment
  , KindEnv
  , emptyKindEnv
    -- * The coalgebraic unfold
  , kindOf
  , liftTower
  , towerOfView
  , universeStream
    -- * Navigation
  , climb
  , projectFirstRung
    -- * Coinductive comparison
  , compareTowers
  ) where

import Constructor.HyperLite (hRun)
import Constructor.Level (Lv (..))
import Constructor.Syntax (Name)
import Constructor.Tinf (TyErr (..))
import Constructor.TyExpr (TyExpr)
import Constructor.TyProc (TyProc, TyView (..), viewToTy)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

-- | A Tower is its horizontal 'TyView' at the current rung paired
--   with the (lazily-evaluated) Tower one rung above.  The vertical
--   slot is intentionally lazy — this is codata, finite generators
--   yielding potentially-infinite unfoldings.
data Tower = Tower
  { horizontal :: !TyView
  , vertical   :: Tower
  }

-- | Map from a declared type-constructor name to its kind annotation
--   (the @K@ in @data X : K@) as a 'TyProc'.  Built by 'HypTinf'
--   while elaborating each @data@ declaration; consumed by 'kindOf'
--   when unfolding the vertical of a Tower.
type KindEnv = Map Name TyProc

emptyKindEnv :: KindEnv
emptyKindEnv = Map.empty

-- | The coalgebraic one-rung-up unfold step (PLAN's "tail-then-head
--   as coalgebraic inference" step 2).  Given the horizontal view at
--   rung @n@, return the horizontal view at rung @n+1@ — i.e., the
--   kind of the current rung.
--
--   The cases:
--
--   * 'TyConV' (a declared tycon): look up its kind annotation in
--     the env; fall back to @*0@ if absent (built-ins, or empty env
--     in synthetic tests — preserves backward compatibility with the
--     commit-7 synthetic universe-stream tests).
--
--   * 'TyAppV' f _: result kind of f.  For our limited grammar where
--     tycon kind annotations are flat (the result kind only, not
--     an arrow-shaped @K1 -> K2@), recursing on the head gives the
--     right answer.  A later commit can refine this when explicit
--     parameter-kind annotations land.
--
--   * 'TyArrV' a _: homogeneous arrow — either side's kind is the
--     arrow's kind.
--
--   * 'TyVarV': defaults to @*0@ (the implicit parameter kind in our
--     grammar; an explicit @data List (a : K)@ feature would refine
--     this).
--
--   * 'TyUnivV' lv: the kind of universe-at-@lv@ is universe-at-@S
--     lv@.
--
--   * 'TyMetaV': propagates as a meta (kind unknown).  Tower arc
--     step 3 will treat this as a fresh kind-meta to be unified
--     during tower-aware 'meet'.
kindOf :: KindEnv -> TyView -> TyView
kindOf env v0 = case v0 of
  TyConV n _   -> case Map.lookup n env of
                    Just kindProc -> hRun kindProc
                    Nothing       -> TyUnivV (S (S Z))   -- fallback: @*0@
  TyAppV f _   -> kindOf env (hRun f)
  TyArrV a _   -> kindOf env (hRun a)
  TyVarV _ _   -> TyUnivV (S (S Z))                      -- parameters default to @*0@
  TyUnivV lv   -> TyUnivV (S lv)
  TyMetaV m    -> TyMetaV m

-- | Lift a 'TyProc' to a Tower under a given 'KindEnv'.  The
--   horizontal is the proc's TyView; the vertical is generated
--   coinductively by 'kindOf'.
liftTower :: KindEnv -> TyProc -> Tower
liftTower env p =
  let v = hRun p
  in Tower v (towerOfView env (kindOf env v))

-- | Coalgebraic unfolding: the Tower whose horizontal is the given
--   view and whose vertical is 'kindOf' applied repeatedly.
--   Productive codata as long as 'kindOf' produces a different view
--   each step (it does, because the @Lv@ strictly increases inside
--   the @*n@-stable tail; the structural layer is finite).
towerOfView :: KindEnv -> TyView -> Tower
towerOfView env v = Tower v (towerOfView env (kindOf env v))

-- | Convenience: the universe-only tower starting at a given level.
--   Special case of @towerOfView emptyKindEnv (TyUnivV lv)@ — what
--   the @*n@-stable tail looks like in isolation.
universeStream :: Lv -> Tower
universeStream lv = towerOfView emptyKindEnv (TyUnivV lv)

-- | One step up the tower (the directed @:@-arrow).  Total but
--   irreversible — there is no inverse function because the
--   @:^{-1}@ relation is many-to-one over all preimages.
climb :: Tower -> Tower
climb = vertical

-- | Project the first rung's horizontal view back to a 'TyExpr'.
--   For a Tower whose horizontal is a metavariable-free TyView,
--   this is the parity invariant against today's 'procToTy':
--
--   @
--   projectFirstRung (liftTower env p)  ==  procToTy p
--   @
--
--   (regardless of @env@ — the env affects only the vertical).
projectFirstRung :: Tower -> TyExpr
projectFirstRung = viewToTy . horizontal

-- | Coinductive comparison of two Towers along the vertical axis.
--
--   Walks both towers rung-by-rung, comparing horizontal views.
--   Termination is guaranteed by the @x^0 = 1@ collapse from PLAN's
--   covering-space framing: every Tower's vertical eventually
--   stabilises into a pure @*n@-stream tail, and two such tails
--   coincide iff they share the same @Lv@.
--
--   Base case (success): both rungs are 'TyUnivV' at the same level.
--   From this point both towers are observationally the same
--   @*n@-stream, so 'Right ()' is sound.
--
--   Failure: at some rung the horizontals diverge structurally
--   (different head shapes, or same shape with different identifying
--   data — Name + Path).  Returns 'TyMismatch' with the diverging
--   rung's views materialised as 'TyExpr'.
--
--   Recursive case: heads are structurally compatible and not yet
--   stable — climb one rung in both towers and continue.
--
--   The comparison is shape-and-identity at each rung (not deep
--   structural equality of TyApp/TyArr children) — children share
--   the same kind by construction (kindOf only inspects the head
--   for those forms), so the rung-1+ comparison handles compound
--   shapes uniformly.
compareTowers :: Tower -> Tower -> Either TyErr ()
compareTowers = go
  where
    go t1 t2
      | TyUnivV lv1 <- h1, TyUnivV lv2 <- h2
      , lv1 == lv2                       = Right ()
      | sameView h1 h2                   = go (vertical t1) (vertical t2)
      | otherwise                        = Left (TyMismatch (viewToTy h1) (viewToTy h2))
      where
        h1 = horizontal t1
        h2 = horizontal t2

    sameView v1 v2 = case (v1, v2) of
      (TyConV n1 p1, TyConV n2 p2) -> n1 == n2 && p1 == p2
      (TyVarV n1 p1, TyVarV n2 p2) -> n1 == n2 && p1 == p2
      (TyUnivV l1,   TyUnivV l2)   -> l1 == l2
      (TyMetaV m1,   TyMetaV m2)   -> m1 == m2
      (TyAppV{},     TyAppV{})     -> True
      (TyArrV{},     TyArrV{})     -> True
      _                            -> False
