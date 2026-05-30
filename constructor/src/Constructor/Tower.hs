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
    -- * Coinductive comparison + unification
  , compareTowers
  , meetTowers
  ) where

import Constructor.HyperLite (hPure, hRun)
import Constructor.Level (Lv (..))
import Constructor.Syntax (Name)
import Constructor.Tinf (TyErr (..))
import Constructor.TyExpr (TyExpr)
import Constructor.TyProc
  ( Subst
  , TyProc
  , TyView (..)
  , emptySubst
  , meet
  , resolveView
  , viewToTy
  )
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
--     commit-7 synthetic universe-stream tests).  Self-reference
--     special case: when the kind annotation IS the same TyConV
--     (modulo offset) — the @data Weird : Weird@ shape — return the
--     same TyConV with the offset bumped by one rather than
--     recursing into a stationary stream.  This is the productive
--     codata that the Weird-style stratification needs.
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
-- Subst-aware: the first action is 'resolveView s' on the input.
-- This is the naturality fix — making 'kindOf' a natural family
-- indexed by 'Subst', so the square
--
--       kindOf s
--   v  ─────────►  kindOf s v
--   │                 │
--   resolve s'        resolve s'
--   ▼                 ▼
--   resolve s' v ─►  kindOf s' (resolve s' v)
--       kindOf s'
--
-- commutes against substitution extension @s ⊑ s'@.  Without
-- 'resolveView' at entry, 'kindOf' specialises at @s = ∅@ and the
-- square breaks the moment a meta is bound — climb-then-resolve and
-- resolve-then-climb land at different views, the upward chain
-- diverges from the substitution-coherent one, and tower-aware
-- meet against a bound meta produces stale upper rungs.
kindOf :: Subst -> KindEnv -> TyView -> TyView
kindOf s env v0 = case resolveView s v0 of
  TyConV n p offset -> case Map.lookup n env of
                         Just kindProc -> case hRun kindProc of
                           -- Self-reference: kindProc IS our own TyConV.
                           -- Bump the deck-shift offset instead of recursing
                           -- — produces 'Weird@(offset+1)', the next rung
                           -- of the Weird-tower as productive codata.
                           TyConV n' p' _
                             | n == n' && p == p' -> TyConV n p (S offset)
                           other -> other
                         Nothing -> TyUnivV (S (S Z))   -- fallback: @*0@
  TyAppV f _   -> kindOf s env (hRun f)
  TyArrV a _   -> kindOf s env (hRun a)
  TyVarV _ _   -> TyUnivV (S (S Z))                      -- parameters default to @*0@
  TyUnivV lv   -> TyUnivV (S lv)
  TyMetaV m    -> TyMetaV m   -- after resolveView, this means truly unbound

-- | Lift a 'TyProc' to a Tower under a given 'Subst' and 'KindEnv'.
--   The horizontal is the proc's TyView; the vertical is generated
--   coinductively by 'kindOf'.  The 'Subst' fixes the substitution
--   context at construction time — note that callers who extend the
--   substitution later need to either re-build the tower or walk it
--   via 'meetTowers' (which regenerates each climb under the current
--   Subst rather than walking the frozen 'vertical' chain).
liftTower :: Subst -> KindEnv -> TyProc -> Tower
liftTower s env p =
  let v = hRun p
  in Tower v (towerOfView s env (kindOf s env v))

-- | Coalgebraic unfolding: the Tower whose horizontal is the given
--   view and whose vertical is 'kindOf' applied repeatedly under
--   the given 'Subst'.  Productive codata as long as 'kindOf'
--   produces a different view each step (it does, because the @Lv@
--   strictly increases inside the @*n@-stable tail and the
--   TyConV-stable tail bumps the deck-shift offset; the structural
--   layer is finite).
towerOfView :: Subst -> KindEnv -> TyView -> Tower
towerOfView s env v = Tower v (towerOfView s env (kindOf s env v))

-- | Convenience: the universe-only tower starting at a given level.
--   Special case of @towerOfView emptySubst emptyKindEnv (TyUnivV lv)@
--   — what the @*n@-stable tail looks like in isolation.
universeStream :: Lv -> Tower
universeStream lv = towerOfView emptySubst emptyKindEnv (TyUnivV lv)

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

-- | Tower-aware unification (Tower arc step "tower-aware meet").
--
--   Walks both towers rung-by-rung along the vertical axis, threading
--   a 'Subst' through the rungs.  At each rung the horizontal slot is
--   reconciled by 'Constructor.TyProc.meet' lifted via 'hPure'; this
--   is the /groupoid-flavoured/ symmetric arm of the algebra
--   (metavariable bindings flow into 'Subst', structural mismatches
--   surface as 'TyMismatch').  The vertical walk is the
--   /directed-flavoured/ arm — today it is structurally the same as
--   the horizontal recursion, but the asymmetry is what step 4 and the
--   eventual subtyping/coercion work will specialise.
--
--   Termination is guaranteed by the @x^0 = 1@ collapse: every
--   Tower's vertical eventually stabilises into a pure @*n@-stream
--   tail, and two such tails coincide iff they share the same @Lv@.
--   The base case fires when both rungs are 'TyUnivV' at the same
--   level — from there both towers are observationally identical.
--
--   Limitation: a metavariable resolution at rung @n@ does NOT yet
--   re-generate the towers' verticals for rung @n+1@ onward.  In the
--   current corpus this is moot — the kind-check use site in
--   'Constructor.HypTinf.dataDecl' threads no metavariables — but it
--   is the path that a tower-aware occurs check / vertical
--   regeneration will need to close.
--   Note on regeneration: this walk does NOT use the towers' frozen
--   'vertical' slots after the first rung.  Each climb regenerates
--   via 'kindOf s' env' against the just-extended substitution, so
--   meta-bindings recorded at rung @n@ flow into the upper rungs
--   correctly.  Walking the frozen vertical instead would give the
--   right view at rung @n+1@ (via 'resolveView' inside 'meet') but
--   stale views from rung @n+2@ onward — the staleness only fixable
--   by re-running 'kindOf' under the new Subst.
meetTowers :: KindEnv -> Subst -> Tower -> Tower -> Either TyErr Subst
meetTowers env = go
  where
    go s h1Tower h2Tower = step s (horizontal h1Tower) (horizontal h2Tower)

    step s h1 h2
      -- *n-stable tail: both rungs are TyUnivV at the same level.
      -- This is the canonical termination case for non-self-stratified
      -- towers (everything that's not Weird-style).
      | TyUnivV lv1 <- h1_, TyUnivV lv2 <- h2_
      , lv1 == lv2                       = Right s
      -- TyConV-stable tail (Weird-style stratification): both rungs
      -- are the same TyConV (Name + Path + offset).  Stern-Gerlach
      -- guarantees def-path identification for nullary tycons, and
      -- equal offsets mean both towers have climbed the same number
      -- of self-referential rungs above the def.  From here both
      -- towers are observationally identical productive codata.
      | TyConV n1 p1 o1 <- h1_, TyConV n2 p2 o2 <- h2_
      , n1 == n2 && p1 == p2 && o1 == o2 = Right s
      | otherwise                        = do
          s' <- meet s (hPure h1) (hPure h2)
          step s' (kindOf s' env h1) (kindOf s' env h2)
      where
        h1_ = resolveView s h1
        h2_ = resolveView s h2

-- | Coinductive comparison: 'meetTowers' under the empty kind-env
--   and empty substitution, discarding the resulting 'Subst'.
--   Convenience for callers (tests and shape probes) that only want a
--   yes/no parity verdict and whose towers were already built with
--   the right env baked in (so re-running 'kindOf' under
--   'emptyKindEnv' would be unsound — instead this function walks
--   the towers' pre-existing vertical slots, which is the
--   meta-blind semantics).
compareTowers :: Tower -> Tower -> Either TyErr ()
compareTowers = go
  where
    go t1 t2
      | TyUnivV lv1 <- h1, TyUnivV lv2 <- h2
      , lv1 == lv2                       = Right ()
      | TyConV n1 p1 o1 <- h1, TyConV n2 p2 o2 <- h2
      , n1 == n2 && p1 == p2 && o1 == o2 = Right ()
      | sameView h1 h2                   = go (vertical t1) (vertical t2)
      | otherwise                        = Left (TyMismatch (viewToTy h1) (viewToTy h2))
      where
        h1 = horizontal t1
        h2 = horizontal t2

    sameView v1 v2 = case (v1, v2) of
      (TyConV n1 p1 o1, TyConV n2 p2 o2) -> n1 == n2 && p1 == p2 && o1 == o2
      (TyVarV n1 p1,    TyVarV n2 p2)    -> n1 == n2 && p1 == p2
      (TyUnivV l1,      TyUnivV l2)      -> l1 == l2
      (TyMetaV m1,      TyMetaV m2)      -> m1 == m2
      (TyAppV{},        TyAppV{})        -> True
      (TyArrV{},        TyArrV{})        -> True
      _                                  -> False
