# Backpressure — an energy economy for narrowing search

**Status:** design, not yet implemented (2026-06-02).  Arose from the
v0.6.0 narrowing work: the Phase-D search can diverge on non-productive
infinite branches, and a fuel bound was rejected in favour of a
physically-motivated *backpressure* model.  The fair-search substrate
it builds on landed in `04b9a2f` (interleave / `>>-`).

---

## The problem

Phase-D narrowing case-splits a stuck meta on the deferred function's
`case` arms, refines, and re-reduces (`solve` in `Constructor.Interp`).
A function whose *recursive* arm is tried first generates an unbounded
branch:

```
f = \n -> case n { S k -> f k; Z -> T };   data Wit (n:Nat) { W : f n -> Wit n };
let rt = W T          -- forces  f ?n ≡ T
```

`?n := Z` is a shallow solution (`f Z = T`), but the `S` arm leads to
`f ?k`, which is stuck again → an all-`S` spine that never reaches a
ground value.

Fair search alone (`interleave` / `>>-`, committed `04b9a2f`) does NOT
fix this: to round-robin two streams, `interleave` must `msplit` the
left one, which runs it *to its first answer*.  A non-productive
infinite branch never produces a first answer, so `msplit` dives it
forever.  **Empirically confirmed: it hangs.**  Fairness needs each
branch to be *productive per step* (yield control / terminate); it
supplies ordering, not finiteness.

## Why not fuel

A per-branch integer depth cap is crude:

- arbitrary magic number — too small rejects legitimate deep solutions,
  too large grinds through `width^depth` dead work before failing;
- not compositional (what fuel for a narrow nested in a narrow?);
- blind to whether a branch is doing useful work — it decrements the
  same whether the branch approaches a solution or spins.

## The physical model — a Mexican-hat energy economy

Picture the search sitting in a **Mexican-hat (sombrero) potential**
`V(r)`: a bump at the centre (epicentre), a circular trough, a rising
rim.

- A **source** = a narrowing path actively emitting constructors.  Many
  coexist (the `choose` alternatives / live branches).
- A **bead** = one emitted constructor, carrying **weight**.  Born at
  the epicentre.  **Weight = 1 + constructor-children** (the node
  itself, plus the `a` frontier slots it opens) — so a nullary `Z`
  weighs `1`, a unary `S` weighs `2`, a binary `Cons` weighs `3`.  The
  `1` is the node that has *arrived* at radius `r`; the `a` are the
  children that still must be *pushed* to `r+1` — which is exactly the
  split in the energy rule below.  **`1 + arity` is just the node's
  memory footprint**: one word for the tag/header plus one pointer per
  child — the heap cell a constructor allocates.  So weight is no knob:
  backpressure charges the search in proportion to the *memory* the
  candidate term would cost to materialise.  Bigger terms cost more
  energy to push out precisely because they cost more memory to build.
- **Radially rigid, vertically flexible**: a bead's *radius* is rigid —
  it equals the number of production-ticks since the bead was born; its
  *height* is whatever the hat says at that radius, `V(r)`.
- **Production is the clock.**  A source that produces pushes its beads
  one radius outward; a source that stops producing freezes its beads
  in place (no march, no energy change).  No separate timer — "easy,
  physics."
- **Down replenishes, up drains.**  A bead sliding down the inner slope
  (epicentre → trough) feeds its released potential energy back into its
  source.  A bead climbing the rim (trough → wall) must be *pushed* —
  it drains the source.
- Every source **starts at ≈ 0 energy**; it **fills** (early beads slide
  into the trough) then **drains** (older beads pile onto the rim).
- **Stall**: when a source can't fund the next push, it stops.
- **All sources stalled ⇒ give up** (UNSAT for this meet).

The runaway `S`-spine self-extinguishes: its old beads pile on the rim
faster than new ones fund it, so it stalls at *finite* depth.  The
shallow `Z` sits in the trough and is reached while energy is cheap.

### The linear special case — a telescope

*Arity-1 chain only.*  The instant a production bifurcates (next
section) there is no single line to collapse and **the telescope is
gone** — keep this picture scoped to the `S`-spine.

Each production, every existing bead slides `r → r+1`, releasing
`V(r) − V(r+1)`.  Summed over a source's contiguous bead-front
(radii `0 .. k-1`) this **telescopes**:

```
ΔE  =  Σ_{r=0}^{k-1} (V(r) − V(r+1))  =  V(0) − V(k)
```

**Why it telescopes (the shift-register picture).**  The beads are a
shift register: on each production every interior bead *takes the place
the bead ahead of it just vacated*, so every interior place is occupied
both before and after — its energy is unchanged and cancels.  Only the
two ends change occupancy: the new bead entering at the centre (`V(0)`)
and **the frontier** — the bead moving into the still-empty spot at
radius `k` (`V(k)`).  Since `V(0)` is a constant baseline, per
production you evaluate the hat **exactly once, at the frontier radius**
(= the current depth).  No sum, no bead-cloud — one `V(·)` call.

### Bifurcation — the front is a tree, not a chain

The telescope assumed every production is arity-1 (the `S`-spine: one
frontier, one continuation).  A **multi-arity** constructor split forks
the front: resolving a meta to `C ?m₁ … ?mₐ` spawns `a` frontier beads
(the sub-metas), so the front is a bead-**tree**, not a chain — **and a
tree does not telescope.**  There is no contiguous line whose interior
cancels, so the `V(0) − V(k)` collapse simply doesn't exist here.

What survives is not the telescope but its *locality*.  Energy is
accounted **per resolution event** — one local delta, evaluated where
the event happens, summed over the resolution tree.  It is cheap
because each delta touches only the resolved bead and its `a` children,
**not** because anything cancels along a chain.  Resolving a frontier
bead at radius `r` to a ctor of arity `a`:

```
E += V(r) − a·V(r+1)
```

- `a = 1` (unary `S`):  `V(r) − V(r+1)` — the linear slide; the *only*
  arity whose per-event deltas chain up into the telescope above.
- `a = 0` (nullary `Z`): `+V(r)` — the track **closes** (a sub-solution);
  the bead's whole weight is `1`, all of it the arrived node, so its
  full height `V(r)` refunds and nothing is pushed.
- `a ≥ 2` (`Cons`/`Pair`/`Node`): `V(r) − a·V(r+1)` — the **fork**: `a`
  beads to push.  The `a` multiplies the *child* term `V(r+1)`, so its
  effect flips sign across the trough.

The rule **is** the weight `1 + a` split across two radii: the `1` (the
arrived node) settles at `r` and *releases* `+V(r)`; the `a` (its
children) are *pushed* to `r+1` and *cost* `−a·V(r+1)`.  Gain for what
slid into place, drain for what must be shoved outward — that sign
asymmetry is the whole engine.  This is "beads carry weight" made
precise: **weight = 1 + arity**.

**Betting bushy is good on the slope, bad on the steep.**  The arity
`a` scales `−V(r+1)`, the height the children land at — and `V`'s sign
turns over at the trough:

- **On the inner slope** (`r+1` still inside the well, `V(r+1) < 0`):
  `−a·V(r+1) > 0` and grows with `a`.  Forking lands `a` children deep
  in the trough → **`a×` the refund**.  Wide-and-shallow *funds* the
  search: bet bushy here.
- **On the rim / steep** (`r+1` up the wall, `V(r+1) > 0`):
  `−a·V(r+1) < 0` and grows with `a`.  Forking drains `a×` faster →
  wide-and-deep is ruinous.  A bushy split on the steep is the fastest
  way to stall.  Bet narrow (`a ≤ 1`) here.

So arity isn't uniformly self-limiting — it's a **bet whose payoff
depends on radius**.  The energy-weighted scheduler should therefore
*prefer* high-arity resolutions while the frontier is cheap (downhill)
and *defer* them once it has climbed the rim — exactly the order that
keeps wide structures shallow and deep structures thin.

**Locality**, not telescoping, is what's cheap: each resolution touches
one frontier bead and spawns its `a` children — `O(arity)`, two hat
evaluations (`V(r)`, `V(r+1)`), no cloud.  The radius is the
ctor-nesting depth, already encoded in the sub-meta's path (the
`PsCtorAppArg` nesting).  The frontier is now a **multiset** of live
sub-metas; the reduction works one at a time (its current stuck
scrutinee), the others **freeze** (no production ⇒ no march ⇒ no flux).

`ΔE > 0` while a resolution lands in the trough (gain); `ΔE < 0` on the
rim (drain).  `E` climbs, peaks, falls; **stall when `E < 0`**.  No
bead-cloud bookkeeping, no fuel integer — just the hat's physical
knob(s).  (`V(r) = r⁴ − c·r²`; the bound emerges from `c`.)

### Why it composes with fair search

A stalling source is a **finite** source (`→ empty` at the rim).  That
finiteness is exactly the per-step productivity `interleave` / `>>-`
needed and lacked.  **Backpressure supplies finiteness; fairness
supplies ordering.**  Together: the `S`-spine stalls (finite) → `msplit`
returns → `interleave` reaches the trough → `Z` found, terminates.

## The quantified refinement — energy-weighted scheduling

Energy need not be just life/death; it can be the **scheduler**.  Each
live source holds a percentage of the *total free energy* across all
sources.  **That percentage = its probability of getting the next
production turn.**

- trough-dwellers (productive, near a solution) command most of the
  energy → most of the turns;
- rim-climbers throttle toward 0 % → effectively dropped;
- total → 0 (all stalled) → give up.

This is a physics-derived **importance / best-first scheduler** —
"best" = "most free energy", no hand-tuned heuristic.

### Two engineering consequences

1. **This is no longer stock `interleave`** (rigid equal-turn
   round-robin).  Energy-weighted turns need an explicit *weighted
   frontier over suspended sources* — a resumption scheduler.  This is
   the machinery the Hyper-LogicT (Kidney/Wu) substrate would provide
   intrinsically; the scheduler is the real justification for moving off
   stock `Logic`, not raw speed.
2. **"Probability" should be deterministic** for a reproducible
   type-checker: weighted / deficit round-robin (turns ∝ energy share),
   *not* an RNG — unless we deliberately want a Las-Vegas search.

## Implementation plan

### Phase 1 — the energy *bound* (rides the existing `interleave`)

Thread a scalar `E :: Double` + `depth :: Int` through `solve` (the
runaway locus; level-1 `narrowArg` is already finite).  Each recursive
split: `E' = E + (V(0) − V(depth+1))`; recurse iff `E' ≥ 0`, else
`empty` (stall).  Deterministic; kills the hang; finds `?n := Z`.
Regression test: the recursive-`S`-first `f` above.  `V(r) = r⁴ − c·r²`,
one knob `c` (well width; depth bound emerges ≈ √c-ish).

### Phase 2 — the energy-*weighted* scheduler

Replace round-robin with a weighted frontier of suspended sources;
each step picks a source with turn-share ∝ its `E`; reinsert or drop on
stall.  Needs the resumption substrate (custom, or Hyper-LogicT).
Deterministic weighted-RR realisation.

**Radius-dependent arity bet** (from "bushy good on the slope, bad on
the steep").  When several resolutions compete, order them by the
*sign of `r+1` relative to the trough*: downhill (`V(r+1) < 0`) prefer
high-arity splits — they refund `a×`; uphill (`V(r+1) > 0`) prefer
`a ≤ 1` — high arity drains `a×` and stalls fastest.  This is just
reading `E += V(r) − a·V(r+1)` as a per-candidate score and picking the
max; no extra knob, it falls straight out of the hat.

## Knobs / open questions

- **Hat shape** `V(r)`: default `r⁴ − c·r²`; `c` = well width.  Other
  shapes (Gaussian-bump, piecewise) are fair game.
- **Bead weight**: settled on `1 + arity` (node + children; binary ctor
  = weight 3).  Uniform-per-constructor is the fallback if the `1 + a`
  split ever proves too aggressive on wide narrowing.
- **Where energy seeds**: per top-level meet, or shared across the whole
  elaboration?  (Phase 1: per `narrowOnce` call, `E₀ = 0`.)
- **Interaction with the occurs/cycle guard** (the still-open `[unsound]`
  review item): both bound the search; sequence them deliberately.

## Provenance

Discussion 2026-06-02 (sombrero / bead / weight / "radially rigid,
vertically flexible" / production-as-clock / energy-share-as-turn-
probability — the user's model).  Builds on the fair-search substrate
`04b9a2f`.  Supersedes the "fuel bound" framing in the v0.6.0 review
note on `e80560d` (which called fuel the next step; backpressure
replaces it).
