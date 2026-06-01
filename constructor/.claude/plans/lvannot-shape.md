# LvAnnot + iso-tower-parametric — design arc for v0.5.0+

## Status (post-v0.4.0)

The five-phase foundation arc **shipped in v0.4.0** (tag commit
61efd8c, 2026-06-01):

| Phase | Commit | Status |
|---|---|---|
| 0. LvAnnot + Shape | b30fc4a | ✅ shipped |
| 1. 'tyKindMeta' AST + parser emission | 968d549 | ✅ shipped |
| 2. 'kindOf' parametric self-loop | cfb4b8d | ✅ shipped |
| 3. Slidability gate in 'reduceDeferred' | e251be2 | ✅ shipped (with cleanup bb013e2) |
| 4. Sugar emits kind-meta default | 61efd8c | ✅ shipped |

v0.5.0-dev (`dfb616c+`) is implementing the carrier overrides that
turn the foundation on end-to-end.  Status:

| Residual | Commit | Status |
|---|---|---|
| R1. HypTwr 'tyKindMeta' override | dfb616c | ✅ landed |
| R3. Use-site resolution + EOE default | — | next |
| R4. kEnv self-applied entries | — | open |
| R2. KindEnv tracks ctor kinds | — | open |

See the git-note on 61efd8c for the full residuals table.

## Context

`v0.3.1` shipped the per-arm Subst-fork and `TyCaseV` (type-level
case-of for divergent-arm bodies).  `v0.4.0`-dev added Haskell-
style data sugar (`data List a = Nil | Cons a (List a)`),
currently desugared to classical-ctor form (each ctor returns
the parametric data applied to its params).

The user's intended desugar was iso-tower for parametric data —
each ctor value its own singleton type, the data as the covering
space.  The discussion captured in the git-note on `2d42e8a`
("Update: functional dependency, slide-time framing") identified
that iso-tower-ness is a **slide-time concern**, not a
data-declaration-time concern: the decision "is List iso-tower
here?" emerges contextually at use sites where the slide
(demote-interp-promote) fires, gated on whether all args are
slidable.

This plan sketches the five-phase arc that delivers iso-tower-
parametric data via that framing.

## Goals

1. `data List a = Nil | Cons a (List a)` parses + elaborates as
   today (classical default preserved).
2. At a use site `List Bool⋮` (where `Bool⋮` is iso-towered), the
   slide engages on slidable args and produces `TyCaseV`-shaped
   refinements for divergent ctor result types.
3. At a use site `List Nat` (where `Nat` is classical), behavior
   is unchanged from today (slide blocks, classical applies).
4. Multi-arg data (`Pair a b`) handled uniformly through the
   same machinery.
5. No regressions in existing tests.

## Non-goals (v0.5.0+ deferrals)

- **Per-slot iso-tower-ness** for mixed-shape data
  (`Tagged a b` with `a` iso-tower, `b` classical): the v0.5.0
  slidability gate is "all-or-nothing".  Per-slot precision is
  a v0.6.0+ refinement.
- **Universe inference for declared params** (`(a : *l)` with
  inferred `l`): out of scope.  The Haskell-style sugar's
  un-annotated params get the new kind-meta treatment, but
  explicit annotations remain locked.
- **Pattern-matching covering-space machinery beyond what
  `TyCaseV` already does**: the slide → TyCaseV path is the
  v0.5.0 mechanism; deeper covering-space pattern matching
  (e.g. arms that pattern-match on the covering relation
  directly) is later work.

---

## Phase 0 — `LvAnnot` extension (plumbing)

### What changes

`src/Constructor/Tc.hs`:

```haskell
data LvAnnot (s :: Sort) where
  LvAExpr :: !Lv -> !Shape -> LvAnnot 'SExpr
  LvADecl :: !Lv -> !Shape -> LvAnnot 'SDecl
  LvAProg ::                  LvAnnot 'SProg

data Shape = Classical
           | IsoTower !Name
           | IsoTowerMeta !MetaId
  deriving (Eq, Show)
```

Update every `LvAExpr lv` callsite to `LvAExpr lv Classical`;
likewise for `LvADecl`.  No semantic change.

### Tests

- All existing tests pass unchanged.
- Add a structural-pattern test asserting the `Shape` field is
  accessible.

### Effort: ~30 min (mechanical).

### Dependencies: none.

---

## Phase 1 — Param-kind metas in `collectParams`

### What changes

`src/Constructor/Parser.hs`, in `bareParam`:

```haskell
bareParam = do
  n <- identifier
  -- Default to a fresh kind-meta instead of relying on
  -- downstream's *0 default.  Resolved at use sites.
  metaAnn <- freshExprAnn
  metaId  <- freshKindMetaId
  pure (n, Just (tyKindMeta metaAnn metaId))
```

May need a new AST node `tyKindMeta` (or reuse `tyMetaRef` at
the kind level if it exists).  Downstream layers (HypLinf,
HypTwr) handle kind metas as `Shape = IsoTowerMeta meta`.

### Resolution policy

- At each use site `D arg₁ … argₙ`: the elaborator meets
  `argᵢ`'s actual kind against `D`'s i-th param meta.  If the
  arg is sticky (`*0`/`*l`), the meta resolves to `Classical`.
  If the arg is iso-towered, the meta resolves to
  `IsoTower argTycon`.
- At end of elaboration, any unresolved kind-meta defaults to
  `Classical` (conservative — matches today's behavior).

### Tests

- Existing: pass (classical default preserves semantics).
- New: `data Pair a b = MkPair a b; let p1 = MkPair True 0` —
  inspect Pair's resolved kind metas: `a → Bool`-kind,
  `b → Nat`-kind.  Confirms per-param resolution.

### Effort: ~2-3 hours.

### Dependencies: Phase 0.

---

## Phase 2 — Parametric self-loop in `kindOf`

### What changes

Today's `kindOf` (`src/Constructor/Tower.hs:178`) self-loops only
on nullary `TyConV self`.  Generalize to parametric:

```haskell
kindOf s env v0 = case resolveView s v0 of
  TyAppV f x ->
    let kf = kindOf s env (hRun f)
    in if isSelfApplied f kf
         then TyAppV (hPure (bumpOffset kf)) x
         else kindOf s env (hRun f)  -- existing fall-through

  TyConV n p offset -> ... existing nullary self-loop ...
  ...

-- 'isSelfApplied f kf' tests whether kf is structurally the
-- same tycon application as f's head, modulo offset.  Care:
-- avoid infinite recursion via kf-resolution depth limit.
```

### Tests

- Existing nullary iso-tower tests (`Bool⋮`, `Nat⋮`, `Iso`,
  `Mirror`, `Swap`, `Weird`) pass unchanged.
- New: `data List⋮ a { Nil; Cons … }` (explicit parametric
  iso-tower syntax) — `kindOf (List a)` returns `List a` with
  bumped offset.  Confirm via the `--types` CLI flag.

### Effort: ~3-4 hours.  Termination invariant requires careful
proof.

### Dependencies: Phase 1 (need kind metas to test
end-to-end).

---

## Phase 3 — Slidability gate in `reduceDeferred`

### What changes

`src/Constructor/Interp.hs`, in `reduceDeferred`:

```haskell
reduceDeferred gs cps subst fname argViews = do
  guard (all (isSlidable subst) argViews)
  ... existing reduction ...

isSlidable :: Subst -> TyView -> Bool
isSlidable s v = case kindOf s env v of   -- 'env' threaded
  TyConV{}    -> True   -- nullary iso-tower
  TyAppV{}    -> True   -- parametric iso-tower (self-applied)
  TyUnivV{}   -> False  -- sticky classical
  TyMetaV{}   -> False  -- conservative: block on unresolved
  TyDeferV{}  -> False  -- block on nested deferred
  TyVarV{}    -> False  -- type variable, sticky in this scope
  _           -> False
```

When the gate fails, reduction returns `Nothing` (existing
fall-through), the deferred application stays opaque.  No
crash, no error — just no progress on the slide.

### Tests

- All existing Phase B/C/D tests pass unchanged (their iso-tower
  args satisfy the gate).
- New: `let pickZ = \n -> case n { Z -> Z; S k -> S Z };
        data Wit : *0 { W : pickZ Bool -> Wit }` — `pickZ Bool`
  (Bool classical, sticky) blocks the slide; W's signature
  stays as an opaque `pickZ Bool` application; W can still be
  declared but its arg type doesn't reduce.
- New: `pickZ Z` (iso-tower Nat⋮, Z slidable) — current Phase C
  behavior, slide engages.

### Effort: ~2 hours.

### Dependencies: Phase 2 (kindOf must return the right shape
for slidability detection).

---

## Phase 4 — Haskell-style sugar emits kind-meta default

### What changes

`src/Constructor/Parser.hs`, in `haskellStyleBody`:

```haskell
-- Before (current, post-v0.4.0-dev):
--   starAnn <- freshExprAnn
--   let e = star starAnn 0          -- *0 default

-- After:
metaAnn <- freshExprAnn
metaId  <- freshKindMetaId
let e = tyKindMeta metaAnn metaId    -- kind-meta default
```

The Haskell-style sugar's data kind becomes a meta, resolved
based on use-site context.

### Tests

- `data List a = Nil | Cons a (List a)` over classical `Nat`:
  still works as today.  Classical kind for both List and a.
- `data List a = Nil | Cons a (List a)` over iso-tower `Bool⋮`:
  List Bool⋮ resolves to iso-tower-parametric; `length` on
  `xs : List Bool⋮` produces `TyCaseV`-shaped refinements via
  the slide.
- Mixed `data Pair a b = Pair a b` use sites — see
  multi-arg tests below.

### Effort: ~2 hours.

### Dependencies: Phases 1-3 (each piece's machinery in
place).

---

## Multi-arg coverage (cross-cutting)

Each phase covers arbitrary arity:

- **Phase 1**: per-param kind metas, allocated independently.
  No arity limit.
- **Phase 2**: `kindOf`'s parametric self-loop recurses through
  `TyAppV` heads — handles `D a b c …` of any depth.
- **Phase 3**: `all (isSlidable subst) argViews` explicitly
  iterates over the argument list.
- **Phase 4**: per-param defaults inherit from Phase 1.

### Multi-arg tests

- `data Pair a b = Pair a b; let p = Pair True 5` —
  `a` resolves to Bool-kind (classical), `b` to Nat-kind
  (classical).  Pair's kind: `*0 → *0 → *0`.  Classical.
- `data Pair a b = Pair a b; let p = Pair True⋮ Z⋮` (iso-tower
  args) — `a` resolves to `Bool⋮`, `b` to `Nat⋮`.  Pair's kind:
  `Bool → Nat → Pair Bool Nat`.  Iso-tower-parametric.  Slide
  on `Pair True⋮ Z⋮` engages.
- `data Pair a b = Pair a b; let p = Pair True⋮ 5` (mixed) —
  `a` resolves to `Bool⋮`, `b` to `Nat` classical.  Slide
  on `Pair True⋮ 5` BLOCKS (Phase 3 gate's all-or-nothing).
  Classical behavior applies; ctor types remain classical;
  no TyCaseV emission.

### Per-slot precision (deferred)

The mixed case above conservatively blocks the slide.  In
principle, slot 1's iso-tower-ness could carry singleton
refinement even though slot 2 is classical — but doing so
requires per-slot tracking that the v0.5.0 plan doesn't
include.  Recorded here as a v0.6.0+ refinement:

- Generalize `isSlidable` to return a per-slot mask rather
  than a global Bool.
- `reduceDeferred` produces partial TyCaseV refinement on
  slidable slots only; non-slidable slots stay sticky.
- Pattern matching accommodates the mixed shape.

---

## Cross-cutting concerns

### Kind-meta representation

The plan assumes a `tyKindMeta` AST form, distinct from value-
level `tyMetaRef` (if any).  Either:

- Add `TyKindMeta` to TyView (heaviest but clearest).
- Reuse `TyMetaV` with a path convention indicating
  "kind-position" (lighter, conflates two uses of meta).

Decision: reuse `TyMetaV` with a dedicated path component
(`PsKindMeta` or similar).  Saves an AST constructor; the
`MetaId`'s path machinery already disambiguates.

### Subst integration

Kind metas use the same `Subst` machinery as type metas — same
`MetaId`, same `meetView` flow.  No separate kind-Subst.

### End-of-elaboration default

After `hypTwrProgram` runs, iterate over remaining unresolved
`IsoTowerMeta` and resolve each to `Classical`.  Single
normalization pass, idempotent.

---

## Estimated total effort

| phase | effort | shippable |
|---|---|---|
| 0. LvAnnot extension | 30 min | yes (no semantic change) |
| 1. Param-kind metas | 2-3 hr | yes (defaults preserve today's behavior) |
| 2. kindOf self-loop | 3-4 hr | yes (additive — nullary still works) |
| 3. Slidability gate | 2 hr | yes (existing tests still pass) |
| 4. Sugar kind-meta default | 2 hr | yes (use-site driven, no regression) |

**Total**: ~10-15 hours focused work, 5 commits, each
independently shippable.

## Risks

- **Phase 2 termination**: parametric self-loop in `kindOf`
  needs a depth limit or structural-recursion proof to avoid
  infinite descent on pathological inputs.  Mitigation:
  bound the recursion depth at a static maximum (e.g. 8);
  reject programs that exceed it as ill-kinded.
- **Phase 3 over-blocking**: unresolved kind metas are
  conservatively reported as non-slidable.  If meta
  resolution happens late, slide-time decisions could block
  prematurely.  Mitigation: accept conservative blocking;
  document the failure mode; add re-meet retry as a v0.6.0+
  refinement if it bites.
- **`MetaId` path conflicts**: kind metas and type metas
  share the `MetaId` space.  Need path-encoding discipline
  to keep them disjoint.  Mitigation: dedicated path
  component (`PsKindMeta`) at the kind-meta allocation site.

## When to land

This is v0.5.0+ scope.  v0.4.0-dev's Haskell-style sugar
ships with the classical default (current state) — no
regression while the arc is being implemented.  Each phase
above can land independently on `constructor` branch as a
separate commit; v0.5.0 cuts when Phase 4 is in.
