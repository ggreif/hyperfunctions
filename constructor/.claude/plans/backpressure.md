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
  the epicentre.
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

### The telescoping payoff — one number per source

Each production, every existing bead slides `r → r+1`, releasing
`V(r) − V(r+1)`.  Summed over a source's contiguous bead-front
(radii `0 .. k-1`) this **telescopes**:

```
ΔE  =  Σ_{r=0}^{k-1} (V(r) − V(r+1))  =  V(0) − V(k)
```

So a source is just **one scalar `E`** plus its depth `k`; producing
the next constructor does

```
E += V(0) − V(depth)        -- sombrero V(r) = r⁴ − c·r²  ⇒  ΔE = c·k² − k⁴
```

`ΔE > 0` while `depth < √c` (trough: gain); `ΔE < 0` past it (rim:
drain).  `E` climbs, peaks, falls; **stall when `E < 0`**.  No bead-cloud
bookkeeping, no fuel integer — just the hat's physical knob(s).

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

## Knobs / open questions

- **Hat shape** `V(r)`: default `r⁴ − c·r²`; `c` = well width.  Other
  shapes (Gaussian-bump, piecewise) are fair game.
- **Bead weight**: uniform per constructor, or arity-weighted (a binary
  ctor = 2 beads)?  Affects how fast multi-arg narrowing drains.
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
