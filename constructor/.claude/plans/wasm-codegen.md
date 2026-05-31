# Wasm codegen for the constructor — a `Rise`-grounded vision

**Status:** vision / architecture sketch, developed autonomously
2026-05-31 from the user's intuition that a rise in Wasm *is* the
statically visible call hierarchy, indirect calls truncate the
visible column, and inlining is suspension of the rise.  Not yet an
implementation plan — the queued bullets in `PLAN.md` ("simple-minded
Wasm codegen + 5 bullets") sit beneath this framing.

The aim of this document is to fix the *vocabulary* and the *layering*
before any code lands, so that each subsequent implementation choice
can be expressed as a move in the `Rise`/`(γ)` algebra rather than as
an ad-hoc engineering decision.

## TL;DR

A Wasm program emitted from constructor code is a `Rise` whose:

- **rung profunctor** `p` is the *operational semantics* of a function
  at the current pipeline stage,
- **horizontal slice** at each rung is the function's call-shape
  (caller/callee `Hyper`),
- **vertical column** is the *statically visible call hierarchy* — as
  many rungs deep as the codegen can resolve at compile time before
  an indirect call (or an erased existential, or an open
  abstraction) cuts the column,
- **rise transformations** `p ~~~> p'` are optimisation passes that
  re-express the same rise at a refined operational level (Scott →
  specialised → inlined → `br_table` → `return_call` → raw
  `call_indirect`).

Multiple stacked rises express multiple stacked passes; the highest
rise still visible at the Wasm boundary is the one we serialise to
bytes.  Suspension is inlining; truncation is indirect call;
erasure is the type-level drop that happens at every rung as we move
down the pipeline.

The whole codegen pipeline is then a single sentence: **take the
constructor IR's rise, evolve its rung profunctor down the pipeline
applying suspensions where statically known, leave indirect calls
where it's not, emit the resulting rung's lateral content as Wasm.**

## Layer 0 — `data` declarations as Scott rungs

A `data X⋮ { … }` declaration becomes, in Wasm, a *family of
functions*:

- One constructor function per arm (`X_C₁`, `X_C₂`, …).  Each
  packages its arguments into a closure and returns a `funcref`.
- One eliminator function `X_elim` that takes a value of type `X` plus
  a continuation per arm, and tail-calls the appropriate
  continuation.

Scott encoding is the natural target because each ctor is *just*
"call the i-th branch of the eliminator with my captured args."  No
algebraic data, no tagged unions in linear memory, no GC roots —
the runtime representation is `funcref + captured-args` and the
"dispatch" is `call_indirect` (or, when we can prove all callees,
`br_table`).

In `Rise` vocabulary: each data type contributes **one rung** to the
overall program rise.  The rung's profunctor is
`Hyper Pt Pt` where `Pt` is "Wasm-closure-ref" (a tagged
funcref + capture pointer).  The Hyper at this rung captures the
eliminator's call-shape: it takes a continuation-bundle (Hyper b a)
and produces an a (the selected branch's body).

Multiple data types = multiple rungs at the same level, connected
horizontally via the lateral `TyProc`-style meet.  This is where
`Constructor.Tower`'s existing structure (`Tower = Γ TyView TyView`)
re-uses cleanly — the typing tower and the codegen tower share the
same shape.  The codegen tower is just the *erased* version, with
`Pt` standing in for `TyView`.

```
Wasm-Rise  ::= Γ Pt Pt
Pt         ::= (funcref, capture-ptr)   -- closure representation
Hyper Pt Pt = the function as a continuation-receiver
```

## Layer 1 — the statically visible call hierarchy *is* a rise

The user's central intuition: the column of a `Wasm-Rise` is **as
tall as the codegen can statically see**.

Concretely, suppose the IR has:

```
f x = g (h x)
g y = i y
h z = j z
i  w = w + 1
j  v = v * 2
```

If we know all callee identities at codegen time, the call tree
`f → g → i` and `f → h → j` are *visible* — each direct `call $i`
in Wasm is a one-rung step in the rise.  The full rise:

```
rung 0 :   f's body, containing call $g, call $h
rung 1 :   g's body (call $i), h's body (call $j)
rung 2 :   i's body, j's body
rung 3 :   ⟂  (no further direct calls)
```

is observable to the codegen — every rung is a Wasm function and
every transition between rungs is a `call` instruction with a known
target.

The column **terminates** when we run out of statically known
callees.  Three ways that happens:

1. **Indirect call** — `call_indirect $tbl[idx]`.  We don't know
   which function gets called; the rise truncates here.  What's
   above the truncation is *runtime data* (the function table).
2. **External / imported function** — call into the host
   environment.  Equivalent to indirect from the static view.
3. **Recursive call** — the column would be infinite; we don't
   actually want to climb it, we just want to emit the recursive
   `call` instruction.  Treated as truncation for codegen purposes
   (the loop carries the rung structure dynamically).

So the rise has a *static depth*, bounded by the indirect-call /
recursion / imports cut.  Codegen explores it as far as it can,
emits Wasm at each rung, then leaves a `call_indirect` / `loop` /
import to bridge the truncation.

## Layer 2 — optimisation passes are profunctor evolutions

The user's second intuition: optimisation is **`p ~~~> p'`**, a
transformation that replaces the rung profunctor with a refined
version.  Each pass is a functor on rises:

```
Pass : Γ pₖ Pt Pt → Γ pₖ₊₁ Pt Pt
```

Pipeline stages (broad → fine):

| stage   | profunctor `pₖ`                                | what each rung carries                              |
|---------|------------------------------------------------|-----------------------------------------------------|
| 0 (IR)  | `IR.Expr`                                       | abstract syntax, source-level                       |
| 1       | `ANF.Expr` (administrative normal form)        | every subexpression named, no nesting               |
| 2       | `CPS.Expr` (continuation passing)              | continuations explicit                              |
| 3       | `Closure.Expr` (closure converted)             | captures explicit, no free variables                |
| 4       | `Scott.Expr` (Scott-encoded)                   | data ctors and elims are functions                  |
| 5       | `Direct.Wasm` (direct calls only)              | every callee statically known                       |
| 6       | `Tabled.Wasm` (indirect calls minted)          | unknown callees indexed in a function table         |
| 7       | `Final.Wasm` (byte sequence)                   | the emitted Wasm module                             |

Each `pₖ ~~~> pₖ₊₁` is a separate codegen pass.  The whole pipeline
is the composition.  *Multiple high-rises* = the sequence of stacked
towers, each derived from the previous via one pass.

Crucially: **the rise shape doesn't change between stages** (the
visible call hierarchy is *the same*).  What changes is the lateral
content `p` at each rung.  Each rung's `Hyper Pt Pt` body gets
refined; the column's height stays the same until a pass introduces
a truncation (typically pass 6, where some callees go indirect).

This is why "profunctor evolution" is the right framing: passes
preserve column structure and only refine the rung profunctor.

## Layer 3 — inlining is suspension, indirect calls are truncation

The two structural moves on a rise have direct Wasm-codegen meanings:

### Suspension = inlining

Inlining a function `g` into its caller `f`:

- Before: rung k contains `f`'s body with `call $g`; rung (k+1)
  contains `g`'s body.
- After: rung k contains `f`'s body with `g`'s body substituted
  in-line; rung (k+1) is *gone* (or rather, fused into k).

In `Rise` ops: `retreat (collapse [f_rung, g_rung], rest)`.  The
collapse is the substitution — `g`'s body becomes a `block` (or just
inlined sequence) inside `f`'s.  Standard inlining; algebraically a
suspension.

When *all* of an eliminator's branches are inlined simultaneously,
the eliminator's `call_indirect` collapses to a `br_table` — every
branch is a local `block` and the dispatch picks one via `br_table`
at compile time.  This is the "Scott + br_table" perfection: every
known-callee eliminator becomes a zero-overhead jump table.

### Truncation = indirect call

When the codegen can't statically resolve the callee:

- The rung that *would* contain the callee's body is unobservable
  from this point.
- We emit `call_indirect` with the appropriate function-table index.
- The function table itself carries the (statically-emitted) callees;
  what's not known is *which one* will be picked at runtime.

In `Rise` ops: the column **truncates** at this rung.  Above the
truncation is runtime data (the function-table mapping).  We can't
`squash` past a truncation.

`KnownRise` (the level-aware variant in `PLAN.md`) would naturally
type this: rungs below the truncation have level `'S^k 'Z`; above
the truncation, level becomes `⊤` (or a designated opaque token).
The codegen can statically check "this rung is at level < ⊤" to
decide whether to emit direct or indirect.

### Tail call = horizontal step reused

Wasm's `return_call` (and `return_call_indirect`):

- Caller's frame disappears at the call site.
- Callee occupies the caller's stack slot.
- Algebraically: the "current rung" is *replaced* by the callee
  rung; not pushed.

In `Rise`: tail call is `current ← stepUp current` — overwrite,
don't grow.  The visible column doesn't lengthen; it just shifts
one rung up.  Perfect for Scott eliminators where every arm
tail-calls its continuation by construction.

## Layer 4 — Wasm instructions as rise specialisations

Each (γ)/Rise codegen choice maps to a specific Wasm instruction:

| Rise operation                              | Wasm instruction          |
|---------------------------------------------|---------------------------|
| direct call, push frame                     | `call $f`                 |
| direct tail call, replace frame             | `return_call $f`          |
| indirect call (truncation)                  | `call_indirect $tbl[idx]` |
| indirect tail call                          | `return_call_indirect`    |
| eliminator with all branches inlined         | `br_table` over blocks    |
| recursion                                    | `loop` + branch           |
| suspended (inlined) call                     | no instruction; body inlined |
| host import (truncation, external)           | imported `func`           |

The codegen's job per rung is: pick the *cheapest* instruction
consistent with the rise's structure at that rung.  The cost order is
roughly:

```
no instruction (inlined)  <  br_table  <  return_call  <  call
                                                          <
                          <  return_call_indirect  <  call_indirect
```

So: prefer inlining → prefer `br_table` → prefer direct →
prefer tail → only indirect when forced.  Each preference is an
algebraic move on the rise (suspend / collapse / step / truncate).

## Layer 5 — `KnownRise` for level-aware codegen decisions

The relative `Rise` substrate (from `Constructor.HyperRise`) handles
the structure.  The codegen *also* wants to know **how deep the
visible column goes** at each rung — i.e., the absolute level
information that `KnownRise` (per `PLAN.md`'s "Absolute version"
subsection) provides.

Use cases:

- **Inlining budget.**  Inline only rungs at level ≤ `inline_depth`;
  past that, keep direct calls.  Without `KnownRise`'s level type,
  the budget would have to live as a value-level counter; with it,
  the codegen has a static handle on "where am I in the call tree."

- **Tail-call detection.**  `return_call` is legal only when the
  caller's rung is at level n and the callee's body doesn't need to
  preserve the caller's frame.  Type-witness via `KnownRise`'s
  `succ`: a tail call moves `lvl → succ lvl` *replacing* the current
  rung; type-checks the invariant.

- **Truncation as level-⊤.**  An indirect-call boundary moves the
  level to a designated "opaque" successor.  Once at `⊤`, subsequent
  rungs are unknown; the codegen emits indirect calls and stops
  trying to climb.

- **Specialisation gates.**  Some optimisations (e.g., constant
  propagation through `Hyper` self-application) only apply at
  certain rungs.  Gating by level keeps the pass total.

So the *practical* path forward isn't to implement `KnownRise`
immediately — it's to start with `Rise`-grounded codegen and surface
where level-typing would clean up the architecture.  Those surface
sites become the queue for the `KnownRise` implementation.

## Layer 6 — erasure as the irreversible Wasm-bound move

Recall: rise/retreat is reversible (retraction); erasure is
irreversible.  In Wasm codegen, erasure happens at *every rung* as
we move down the pipeline:

- IR `Expr` → ANF: types still present, but reduced to first-order.
- ANF → CPS: no further erasure; structural change only.
- CPS → Closure-converted: capture-env types collapse into "pointer
  to capture record."
- Closure → Scott: type-level dispatch info (e.g., refining-GADT
  index) erases — the runtime sees only the chosen branch.
- Scott → Direct.Wasm: function signatures collapse to Wasm
  types (i32, i64, …); abstract closure types become `funcref +
  capture-ptr`.
- Direct → Final: bytes; no types at all.

Each step erases something.  By the time we emit bytes, the *only*
information surviving is what the runtime needs.  The (γ)/Rise tower
has been compressed to a single rung — the runtime rung — and
everything above has been suspended / fused / erased.

This is the picture from the `38d9ed6` git-note made operational:
"the runtime never moves; it just hosts more and more of the tower
as socle moves get applied."  The Wasm codegen is *the entire socle-
extension sequence* applied to the constructor's IR.

## Layer 7 — concrete starting plan

Drawing the layers together, here's the concrete-but-not-prescriptive
ordering for getting something running:

1. **Pick `Pt`.**  Wasm closure representation — probably
   `{funcref, capture-ptr}` as a 64-bit value or a struct in linear
   memory.  Reflects the choice on top of `Constructor.HyperRise`.

2. **Implement the IR-side rise**, `Γ IR.Expr Pt Pt`.  Each rung is
   a function whose `Hyper Pt Pt` body is its IR-level operational
   semantics.  Uses `Gamma` directly; no new code on the substrate
   side.

3. **Implement passes 1-4** (ANF → CPS → Closure → Scott) as
   `Γ pₖ Pt Pt → Γ pₖ₊₁ Pt Pt` rung-by-rung transformations.  Each
   is a `fmap`-style traversal of the rise.

4. **Implement pass 5** (Scott → Direct.Wasm).  This is where the
   actual Wasm instructions get emitted.  Each rung becomes a
   Wasm function.

5. **Implement pass 6** (truncation discovery).  Walk the rise; mark
   rungs where the visible column ends.  Insert a function-table
   entry and emit `call_indirect` at those boundaries.

6. **Implement pass 7** (bytes).  Serialize the Wasm module.

7. **Implement the inlining suspension.**  Whenever a direct call's
   callee is statically known *and* fits the inline budget,
   `retreat (collapse [caller, callee], rest)` — fuse the rungs at
   the IR level *before* pass 5 emits them as separate functions.

8. **Implement `br_table` collapse.**  When an eliminator's *all*
   branches are inlinable, emit one `br_table` instead of a
   `call_indirect`.  This is the "Scott + br_table" perfection
   mentioned in the `38d9ed6` git-note.

9. **Implement `return_call`.**  Wherever the IR ends with a call
   in tail position, emit `return_call` instead of `call`.  Scott
   eliminator arms are the textbook case.

10. **Add `KnownRise` when (5–9) all want it.**  Don't implement
    pre-emptively; surface the need from the codegen's own
    architecture.

## The 5 bullets revisited (from `PLAN.md`)

The 5 already-queued bullets fit cleanly into this layering:

| bullet                                          | Wasm/Rise interpretation                              |
|-------------------------------------------------|------------------------------------------------------|
| `@`-binders for Build (cyclic data via DPS)     | DPS = (γ)'s "settling fixpoint"; an `@`-binder names the cell at allocation time, and the cycle closes by patching the cell after the body emits — Wasm-side: `i32.store` into the captured slot |
| `λ` and value-level function application         | a `λ` introduces a fresh rung; application invokes it.  Pass-4 (Scott) treats this as a closure ctor + eliminator |
| Non-regular nested data in Scott                | each level of nesting is a separate rung; codegen emits one function per nesting level (or inlines if known) |
| Refining GADT with existentials (Refl shape)    | the indexed-eliminator's Wasm shape is `call_indirect $tbl[idx]` where `idx` is the *refinement evidence* (existential metadata erased) |
| Specialised lint carrier for duplicate-binders  | not a Wasm concern; orthogonal pass |

All five except the last are direct consequences of the rise framing.
The first four would all benefit from `KnownRise`'s level-typing once
the codegen surfaces the need.

## Connection to existing constructor code

What's *already in tree* and ready to plug into this codegen:

- `Constructor.HyperRise` — the `Rise` substrate, the `Gamma`
  carrier, the `Γ` alias.  Wasm codegen would instantiate
  `Γ Pt Pt` for `Pt = closure-ref`.
- `Constructor.Tower` — the typing tower (`Γ TyView TyView`).  Each
  Wasm rung's *type* is a `Tower` rung; the codegen erases this to
  `Pt`.
- `Constructor.Scott` — already emits Scott-encoded Haskell.  The
  Wasm codegen would emit Wasm bytes instead, using the same
  encoding regimes (non-parametric / non-refining parametric /
  refining parametric).
- `Constructor.HypTwr` — the value-level typing pass.  Its output is
  the input for the Wasm pipeline.

What's *missing*:

- A `Pt` type (closure representation).
- The `IR.Expr` … `Final.Wasm` profunctor types and the passes
  between them.
- A function-table builder for indirect calls.
- The inlining / `br_table` / `return_call` decision logic.
- A Wasm bytecode emitter (or use an existing Haskell Wasm lib).

The substrate (`Rise`) covers the structure; everything else is
"fill in the lateral content per stage."

## Why this framing matters

Once the codegen is expressed in `Rise` terms, three things follow:

1. **Each optimisation is algebraic.**  Inlining = suspension.
   `br_table` collapse = composition of suspensions.  Tail call =
   horizontal step.  Indirect call = truncation.  The optimiser
   doesn't pick from an unrelated grab-bag of tricks; it picks
   *which (γ) simplification to apply at this rung*.

2. **The pipeline composes cleanly.**  `pₖ ~~~> pₖ₊₁` are functors
   on the rise; composing them is just composing the functors.
   New passes slot in without rebuilding the framework.

3. **The connection to typing is intrinsic.**  `Constructor.Tower`
   uses `Γ TyView TyView`; the codegen uses `Γ Pt Pt`.  Both are
   `Γ` over different lateral types.  The relationship between
   them — *erasure* — is just a `fmap` from the typing tower to the
   codegen tower, dropping type-rung information rung-by-rung.

This is the picture the `38d9ed6` git-note promised but didn't
operationalise: "the calling convention is the encoding is the
algebra."  Wasm codegen, expressed in `Rise` terms, makes that
identity manifest in actual emitted bytes.

## References

- `Constructor.HyperRise` (in `~/hyperfunctions/constructor/src/`) —
  the substrate.
- `~/hyperfunctions/constructor/PLAN.md` — "Hyper-rise" section and
  "Absolute version: `KnownRise`" subsection.
- Git-note on `38d9ed6` in `~/hyperfunctions` — the calling-
  convention-as-(γ) framing.
- `~/opetopic/.claude/plans/opetope-as-rise.md` — the parallel
  polynomial-functor encoding for opetopes.  Same `Rise` substrate,
  different lateral content; further evidence that `Rise` is the
  right shared foundation.
- Wasm spec, especially the tail-call extension (`return_call`,
  `return_call_indirect`).
- `~/motoko/src/codegen/instrList.ml` — the concrete diff-list-of-
  Wasm-fragments profunctor that this plan adopts as the inner-rise
  `p`.  See "Concrete `p` choices" below.

---

# Finer-grained vision (developed against `~/motoko/src/codegen/`)

The motoko compiler's Wasm backend gives us a concrete, battle-tested
instantiation of every concept above.  Reading
`~/motoko/src/codegen/instrList.ml` and `compile_common.ml` exposes
exactly what shape `p` takes at the instruction level, what shape
the function table takes at the program level, and what peephole
opts naturally fall out as `Rise` operations.  This appendix grounds
the abstract layering in those choices.

## Concrete `p` choices — the **diff-list-of-Wasm-fragments** profunctor

The user's nudge: `p = diff-list of Wasm fragments`.  Motoko's
`InstrList.t` makes this exact:

```ocaml
type t = int32 -> Wasm.Source.region -> instr list -> instr list
```

Translating to Haskell:

```haskell
type Depth   = Int32
type Region  = Wasm.Source.Region
type WasmFrag a b = Depth -> Region -> [Instr] -> [Instr]
-- Specialised: a = b = [Instr], so this is endo-shaped:
-- WasmFrag = Reader (Depth, Region) (Endo [Instr])
```

Properties of this `WasmFrag`:

- **`a = b = [Instr]`.**  Each fragment maps `[Instr] → [Instr]`,
  i.e., it's an endomorphism on instruction lists.  This is the
  *endo-tower* shape from the suspension discussion: the lateral
  types coincide, so `Monoid (p a a)` is automatic.  `mempty` is
  `nop = fun _ _ rest -> rest`; `(<>)` is the diff-list concat
  `(^^) is1 is2 = fun d pos rest -> is1 d pos (is2 d pos rest)`,
  literally function composition under the Reader.
- **Reader of two pieces of context.**  `Depth` is the current
  enclosing-block depth (for `Br N` resolution); `Region` is the
  source-position tag (for DWARF/debug info).  Both are threaded
  through every fragment.
- **Concat is `O(1)`.**  Crucial: this is the *whole point* of
  the diff-list shape.  Building a Wasm function by stitching
  small fragments via `(^^)` doesn't quadratically blow up; each
  `(^^)` is just function composition.

So our concrete codegen profunctor at the *instruction level* is:

```haskell
type p = WasmFrag    -- endo on [Instr], plus Reader (Depth, Region)
```

`Γ WasmFrag [Instr] [Instr]` is the canonical inner-rise: a
hyper-rise of instruction-list endomorphisms.  And because the
lateral type is uniform (`[Instr] = [Instr]`), suspension is
well-defined via `Monoid`, exactly as discussed earlier.

## Two granularity levels — outer rise (functions) + inner rise (instructions)

A Wasm program has two natural rise structures, one nested inside
the other:

- **Outer rise:** *functions*.  One rung per Wasm function.  Direct
  calls (`call $f`) are vertical edges.  `p_outer = WasmFunction`
  (signature + body + locals + …).
- **Inner rise:** *instructions within a function*.  One rung per
  instruction.  Sequence is the column.  `p_inner = WasmFrag` as
  above.

```haskell
type FunctionRise = Γ WasmFunction Pt Pt           -- outer
type InstrRise    = Γ WasmFrag [Instr] [Instr]     -- inner
```

These compose: a `WasmFunction` is built by emitting an `InstrRise`
into its body.  So conceptually `WasmFunction = (signature, InstrRise)`
where the inner rise produces the bytes.

The same `Rise`-algebra applies at both granularities:

- **Outer-level suspension** = inlining a function body into its
  caller's body.  Two function-rungs collapse to one; the inner
  rise of the callee gets concatenated into the inner rise of the
  caller.
- **Inner-level suspension** = peephole opt: two adjacent
  instructions collapse to one.  `LocalSet n + LocalGet n →
  LocalTee n`, `Const + Drop → ε`, etc.  Each peephole rule IS a
  one-rung suspension on the inner rise.

Motoko's `optimize : instr list -> instr list` is *exactly* this
inner-rise suspension cascade, applied as a single zipper-pass over
the emitted list:

- `LocalSet n :: LocalGet n :: rest  →  LocalTee n :: rest`
- `Const _    :: Drop      :: rest  →  rest`
- `LocalGet n :: LocalSet n :: rest  →  rest`  (when n matches)
- `Eq + Const 0 → Eqz` etc.

Every rule is a rewrite that fuses adjacent rungs.  In algebraic
terms: `retreat (collapse [r₀, r₁], rest)` where `collapse` here is
the rewrite-specific reduction.  The whole `optimize` function is an
iterated suspension cascade — *bottom-up rise compression*.

The opportunity that the Rise framing exposes (motoko doesn't have
this explicitly): **peephole rules are algebraic rewrites on
`InstrRise`.**  We could express them as `InstrRise → InstrRise`
transformations and compose them functorially, rather than as a
hand-rolled zipper-traversal.  This is structurally cleaner and lets
each rule be unit-testable in isolation.

## Wasm structured control flow as `KnownRise`

Wasm's structured control flow (`block`, `loop`, `if`, `br N`,
`br_table`) is a perfect concrete instantiation of `KnownRise`:

```
block_type        ::= block | loop | if
br N              ::= "jump to the enclosing block at depth (current - N)"
```

The `N` in `br N` is *the level coordinate*.  `br 0` targets the
innermost enclosing block; `br 1` the next outer; etc.  Motoko's
`InstrList.t` carries `int32` (the depth) precisely because every
`br` resolution needs this level information.

In `KnownRise` vocabulary:

- Entering a `block`/`loop` pushes a level: `succ`-step on the
  carrier.
- Leaving a block pops: `unsuccessor` (not part of `KnownRise`, but
  the dual is "the structural exit").
- `Br N` is the typed jump: it reads as
  `iterate N stepUp current` plus a "break here" semantic — i.e.,
  the level-aware version of stepping up `N` rungs.

Motoko's `depth = int32 Lib.Promise.t` mechanism is interesting:
the depth label is a **promise** that gets fulfilled when the block
is finally emitted (since the depth depends on enclosing context
that may not be known when the inner fragment is built).  This is
*lazy depth resolution* — exactly the kind of thing `KnownRise`'s
type-level levels would resolve at compile time instead.

**`KnownRise` payoff for control flow:** if levels are statically
known, `br N` can be typechecked — guarantee the target block
exists at level `current - N` before code generation.  Today motoko
catches this at validation time (Wasm's structured-control-flow
verifier rejects out-of-range `Br`s); with `KnownRise` it'd be a
compile error.

This is the natural first surface for `KnownRise` to land — exactly
as the PLAN.md "Absolute version" subsection predicted ("Wasm-codegen
story, where call-site/inline decisions are level-sensitive").

## Function table / indirect calls as the rise *truncation*

Motoko's `compile_common.ml` shows the function-table mechanism:

```ocaml
module Table : sig
  type 'a t
  val empty : 'a t
  val add : 'a t -> 'a -> int * 'a t
  val length : 'a t -> int
  val to_list : 'a t -> 'a list
end
```

A fast-append table for things that need to be indexed at runtime —
function pointers, in particular.  An entry in this table is the
boundary where the static rise terminates: from the caller's view,
we know the table index and the table itself, but the *callee* at
that index is opaque (chosen at runtime).

This maps directly to **rise truncation**: the outer rise climbs as
far as direct callees can be statically resolved; at every
`call_indirect`, we stop climbing and instead serialise the
function-table entry.  The table itself is *runtime data*; the
truncation boundary is the codegen-discoverable cut.

So:

- `outer_rise.depth_until_truncation` = how far we can statically
  inline / specialise / `br_table`-collapse
- function table entries = where the rise stops being observable
- `KnownRise` levels could mark this: a designated `⊤` (or a
  `TruncatedAt :: c -> c` successor variant) tags the rung *past*
  which the column is opaque

Codegen logic: walk the outer rise downward, emit Wasm functions for
each rung, stop at `⊤`-rungs and instead emit `call_indirect $tbl[idx]`
plus a table entry.

## Backend duplication — two backends share the substrate

`~/motoko/src/codegen/` has two backends:

- `compile_classical.ml` — classical (orthogonal) persistence
- `compile_enhanced.ml`  — enhanced orthogonal persistence

Both share `instrList.ml` and `compile_common.ml`.  This is a real-
world example of **multiple high-rises** sharing a substrate: both
backends emit the same `InstrRise` shape but with different *content*
at each rung (different layouts, GC discipline, etc.).

In our framework, this reads as: two `Γ WasmFrag [Instr] [Instr]`
instances over the same substrate, differing in which Wasm-fragments
get emitted per IR construct.  The substrate (`InstrList` /
`HyperRise`) is shared; the per-rung content is backend-specific.

Practical implication for the constructor's codegen: design the
codegen as `Γ pₖ Pt Pt → Γ pₖ₊₁ Pt Pt` functors *parameterised by
a backend-specific table of per-construct emitters*.  Different
backends supply different tables; the pipeline structure is shared.
That's exactly what motoko does (the two backends share `InstrList`
and most of `compile_common`).

## Concrete IR-side rise shape

Pinning the IR-side shape based on this:

```haskell
-- Lateral type at the inner rise: instruction stream
type Pt_inner = [Instr]

-- Lateral type at the outer rise: closure handle
data Pt_outer = Pt_outer
  { funcref     :: !FuncIdx       -- index into the function table or direct ref
  , captureSlot :: !MemAddr       -- pointer into linear memory for captures
  , inlineHint  :: !InlineDirective
  }
data InlineDirective = MustInline | MayInline | DontInline | Truncated

-- Outer rise: program structure
type ProgramRise = Γ WasmFunction Pt_outer Pt_outer

-- Inner rise: per-function body
type FuncBodyRise = Γ WasmFrag [Instr] [Instr]

-- A complete Wasm program
data WasmProgram = WasmProgram
  { funcs      :: ProgramRise         -- the outer rise
  , funcTable  :: Table FuncIdx       -- truncation boundary entries
  , globals    :: …
  , memory     :: …
  , exports    :: …
  }

-- Each WasmFunction has a body that is itself an inner rise
data WasmFunction = WasmFunction
  { sig'    :: !FuncType
  , locals  :: ![ValueType]
  , bodyRise :: !FuncBodyRise         -- the per-function inner rise
  }
```

Concretely: a `ProgramRise` is a column of `WasmFunction` rungs;
each rung's `WasmFunction` contains a `FuncBodyRise` (column of
instruction rungs).  Two `Rise`s, one nested inside the other.

## Pipeline passes, concretely

Each pass refines the inner-rise's `p` while preserving the outer-rise
shape (until pass 6 introduces truncations).  Concretely:

| pass     | outer `p`                  | inner `p`                       |
|----------|---------------------------|---------------------------------|
| 1 (ANF)  | `IR.Function`              | `IR.Block` (ANF blocks)         |
| 2 (CPS)  | `IR.Function` (CPS-shaped) | `IR.Block` with continuation arg|
| 3 (CC)   | `Closure.Function`         | `Closure.Block` (captures explicit) |
| 4 (Scott)| `Scott.Function`           | `Scott.Block`                   |
| 5 (Wasm) | `WasmFunction` (direct)    | `WasmFrag` (motoko-shape diff-list) |
| 6 (Tabled)| `WasmFunction` (some indirect) | `WasmFrag`                |
| 7 (Bytes)| serialised module          | n/a                             |

Each pass is `Γ pₖ_outer Pt Pt → Γ pₖ₊₁_outer Pt Pt`, with the inner
rise transformed in lockstep.

Pass 5 (the IR → Wasm pass) is the cliff edge: this is where
abstract semantics become concrete instructions.  Per the motoko
pattern, the bulk of complexity lives here.  The earlier passes are
structural refinements; pass 5 is the "emit code" step.

## Peephole opts as a separate, *post-pass-5* `InstrRise → InstrRise` functor

Motoko applies `optimize` at `to_instr_list` time, after all
fragments are concatenated into a final `instr list`.  That's the
pragmatic choice: peephole rules are local rewrites that need the
adjacency information of a flat list.

In `Rise` terms, this is: after the inner rise is *materialised*
into a flat instruction column, walk that column with a zipper and
apply suspension rules (the peephole-rewrite cascade).  The result
is a *shorter* column with fused rungs.

This could be cleaner if expressed as `InstrRise → InstrRise`
directly, with rules being functorial transformations.  Motoko's
zipper-based traversal works because OCaml is what it is; in Haskell
we could probably express rules more declaratively — `MTL`-style
rewrite passes composed with `(>>>)`.

This is a **codegen-architecture choice** worth keeping a list of:

- (a) post-materialisation zipper (motoko style; pragmatic; works)
- (b) `InstrRise → InstrRise` functor cascade (algebraic; cleaner;
  unknown perf characteristics)

Probably start with (a) for the v0 — motoko's pattern is proven —
and migrate to (b) when peephole opts get rich enough to justify.

## DWARF / debug-info threading

Motoko threads DWARF tags through the instruction stream:
`InstrList` has `Meta` instructions for DWARF tags, plus
combinators like `dw_tag`, `dw_tag_open` that wrap fragments with
metadata.  The Reader-of-(Depth, Region) is precisely the carrier
for "region currently active for source-mapping."

In `Rise` terms: DWARF metadata is *additional lateral content*
attached to each rung.  Either:

- Pack it into the `p`'s state monad (Reader of region + a Writer
  of accumulated DWARF info), or
- Make `p` parameterised by a metadata accumulator type, treating
  DWARF as a side-product.

The motoko pattern (Meta instructions interleaved with real
instructions) keeps things simple — DWARF info rides as actual
list elements, just instructions whose op is `Meta`.  This means
the InstrRise column already carries DWARF; no separate apparatus
needed.

## Summary of the finer-grained vision

The Wasm codegen has *two* nested rises:

1. **Outer rise** over functions (`Γ WasmFunction Pt Pt`).  Visible
   call hierarchy.  Direct calls = vertical edges.  Indirect calls
   truncate.  Inlining = function-level suspension.
2. **Inner rise** over instructions (`Γ WasmFrag [Instr] [Instr]`).
   Diff-list-of-Wasm-fragments per motoko's `InstrList`.
   Concatenation is `O(1)`.  Peephole opts = instruction-level
   suspension.

The pipeline is a sequence of `Γ pₖ → Γ pₖ₊₁` functors at the
outer level, with corresponding inner-level transformations.  The
peephole-opt cascade is a separate post-materialisation pass on the
final `InstrRise`.

Wasm's structured control flow (`block`/`loop`/`br N`) is a natural
`KnownRise`: depth labels *are* level coordinates, and `br N`
typechecks against them.  Function-table entries are the
*truncation boundary* between visible (outer rise climbs) and
opaque (runtime function-table dispatch).

**Two backends share one substrate** (cf. motoko's classical vs
enhanced).  In our framework: two `Γ WasmFunction Pt Pt` instances
over `Constructor.HyperRise`, parameterised by backend-specific
per-construct emitter tables.

Concretely, the constructor's codegen needs:

- `Constructor.WasmFrag` — the inner-rise profunctor, modeled on
  motoko's `InstrList.t`.  Diff-list, Reader of (Depth, Region).
- `Constructor.OuterRise` — the function-level outer rise type;
  `Γ WasmFunction Pt Pt` with `Pt = (FuncIdx, MemAddr,
  InlineDirective)`.
- `Constructor.Wasm.Pipeline` — the sequence of `pₖ → pₖ₊₁`
  passes from IR to bytes.
- `Constructor.Wasm.Peephole` — the inner-rise suspension cascade,
  motoko-shaped.
- `Constructor.Wasm.FuncTable` — the truncation-boundary apparatus.

The substrate (`HyperRise`) provides the rise algebra.  Everything
above is "fill in the lateral content per stage."  No new
abstractions needed.

## Worked example — `data Bool⋮ { T⋮; F⋮ }` through the pipeline

The smallest non-trivial example.  Trace it stage-by-stage to see
the rise's lateral content evolve.

### Stage 0 — Constructor IR (post-`HypTwr`)

The frontend has produced:

```
data Bool⋮ { T⋮; F⋮ }

-- A use site:
case T { T -> F; F -> T }      -- a Bool-flip
```

After `HypTwr` typing, the IR has:

- A type-level `Bool` token (lives at `TyView` rung).
- Two value-level ctors `T :: Bool` and `F :: Bool`, both nullary.
- A `case`-expression with branches `T → F` and `F → T`.

The constructor's existing Scott codegen would emit:

```haskell
newtype Bool' = Bool' { runBool' :: forall r. r -> r -> r }
t', f' :: Bool'
t' = Bool' (\kT _ -> kT)
f' = Bool' (\_  kF -> kF)
elimBool :: Bool' -> r -> r -> r
elimBool b kT kF = runBool' b kT kF
```

That's the Scott encoding.  Now: how does this become Wasm?

### Stage 1 — `Γ IR.Expr Pt Pt` (post-frontend)

Outer rise: 3 rungs.

- Rung 0: `t_ctor` — the ctor function for `T`.
- Rung 1: `f_ctor` — the ctor function for `F`.
- Rung 2: `bool_flip` — the use-site `case T { … }` wrapped as a
  function.  Calls `t_ctor` then `elimBool`.

Plus rung -1: `elimBool` — the eliminator.  In Scott encoding, the
eliminator is *implicit* (it's just `(b kT kF) → b kT kF`); there's
no separate function emitted.  But for clarity let's pretend it has
a rung.

The outer rise's `p = IR.Expr`.  Each rung's `IR.Expr` is an AST node
describing the function's body in source-level vocabulary (no closure
conversion yet, no instructions).

```
Γ IR.Expr Pt Pt
 │
 ├── t_ctor    :: closure (\kT _ -> kT)
 ├── f_ctor    :: closure (\_ kF -> kF)
 ├── bool_flip :: callfun t_ctor; then callfun elim (with branches F, T)
 └── ...
```

### Stage 2 — ANF (administrative normal form)

Each subexpression gets a name.  The outer rise's `p` is now
`ANF.Expr`: still AST-like, but every sub-call has an explicit
binding.

```
bool_flip:
  let v0 = call t_ctor      -- the T
  let v1 = call elimBool v0 -- with branches:
            kT_branch = call f_ctor   -- F
            kF_branch = call t_ctor   -- T (different occurrence)
  return v1
```

Suspension opportunity already visible: `t_ctor` is called twice
in `bool_flip`, once to produce the scrutinee and once as a
continuation.  The first call's result is statically known —
inlining suspends rung 0 into rung 2 at the first call site.

### Stage 3 — CPS

Continuations made explicit:

```
bool_flip(k):
  t_ctor(\v0 ->
    elimBool(v0,
      \kT -> f_ctor(\v1 -> k v1),
      \kF -> t_ctor(\v2 -> k v2)))
```

This is what makes Scott's "every branch tail-calls its continuation"
*structural*: the CPS form makes the tail-call shape explicit.
Every `→` here ends in either another call or `k v` (the outer
continuation), nothing else.

### Stage 4 — Closure-converted

Free variables get explicit captures.  `t_ctor` and `f_ctor` are
top-level so they have no captures; the lambdas in `bool_flip` do.

```
t_ctor :: ClosurePtr
t_ctor = Closure { fnref = $t_body, captures = [] }
$t_body(kT, kF) = kT

bool_flip :: ClosurePtr
bool_flip = Closure
  { fnref = $bool_flip_body
  , captures = []
  }
$bool_flip_body(k) =
  let v0 = invoke t_ctor [k_temp1, k_temp2]
    where
      k_temp1 = Closure $kT_body  [k]    -- captures k
      k_temp2 = Closure $kF_body  [k]
  ... -- and so on
```

At this stage, `Pt = ClosurePtr` is concrete: `(funcref, capture-ptr)`.

### Stage 5 — Direct.Wasm — first concrete instruction emission

Now we materialise instructions.  Each function becomes a Wasm
function; each function's body is built up via `InstrList`-style
fragments.

Outer rise: `Γ WasmFunction Pt Pt`.
Inner rise per function: `Γ WasmFrag [Instr] [Instr]`.

`$t_body` (the body of the `T` ctor's selector function):

```
;; t_body: takes two funcref+capture args (kT, kF), tail-calls kT
LocalGet 0       ;; load kT closure
LocalGet 1       ;; load kT capture
LocalGet 0       ;; (we'd actually load kT funcref via indirect)
... 
CallIndirect $type_continuation
;; or, if we know kT statically (after inlining):
Call $kT_target
```

Or, if inlining has fired (we know `kT = f_ctor` and `kF = t_ctor`):

```
;; t_body inlined into bool_flip; kT is f_ctor whose body is "tail-call k(f)"
;; entire thing collapses to:
Call $f_ctor
```

This is the suspension cascade in action: every direct-call we can
resolve becomes inlined; the residual is a tiny instruction sequence.

`bool_flip` after maximal inlining:

```
;; takes outer continuation k (LocalGet 0)
;; computes T (rung 0 collapsed in)
;; invokes elim with branches F-then-T (rungs 1 and 2 collapsed in)
;; tail-calls k with result
Call $f_ctor     ;; F is the result (flip of T)
LocalGet 0       ;; k
LocalGet 1       ;; k's capture
ReturnCallIndirect $type_continuation  ;; tail-call k with F
```

Three instructions for the whole flip!  Because every call boundary
was statically resolvable, every rung in the outer rise collapsed
via suspension.

The inner rise during construction:

```
emit_bool_flip :: WasmFrag
emit_bool_flip =
     emit_call_f_ctor              -- one fragment
  ^^ emit_localget_k_funcref       -- another
  ^^ emit_localget_k_capture       -- another
  ^^ emit_return_call_indirect     -- final
```

Built with `(^^)`, threaded through Reader (depth, region).

### Stage 6 — Tabled.Wasm (if needed)

In this particular example, every call is direct after inlining, so
the function table is empty.  But if `k` (the outer continuation)
isn't statically known, the `ReturnCallIndirect` needs a table entry:

```
;; If k is statically unknown:
LocalGet 0                          ;; k funcref
LocalGet 1                          ;; k capture
ReturnCallIndirect $type_continuation $table_main

;; Function table:
$table_main = [ ..., $known_k_target_1, $known_k_target_2, ... ]
```

The `$table_main` is built incrementally as the codegen discovers
needs (motoko's `Table` pattern from `compile_common.ml`).

### Stage 7 — Bytes

Serialise.  The whole `bool_flip` becomes ~6 bytes of Wasm:

```
Call    $f_ctor                  ;; 1 byte opcode + LEB128 idx
LocalGet 0                       ;; 1 byte + LEB128
LocalGet 1                       ;; 1 byte + LEB128
ReturnCallIndirect ...            ;; 1 byte + LEB128 + LEB128
```

### Rise evolution recap

| stage | outer `p`              | rungs visible | call edges resolvable |
|-------|------------------------|---------------|----------------------|
| 0     | `IR.Expr`              | 3            | all direct           |
| 1     | `ANF.Expr`             | 3            | all direct           |
| 2     | `CPS.Expr`             | 3            | all direct           |
| 3     | `Closure.Expr`         | 3            | all direct           |
| 4     | `Scott.Function`       | 3            | all direct (Scott elim implicit) |
| 5     | `WasmFunction` (direct)| 3            | all direct           |
| 5+    | after inlining suspensions | 1        | column has collapsed |
| 6     | `WasmFunction` (final) | 1            | empty function table |
| 7     | bytes                  | 1            | ~6 bytes             |

The full lifecycle is: **start with a 3-rung outer rise, suspend it
to a 1-rung outer rise, emit ~6 Wasm bytes.**

For a less aggressive `Bool`-flip use case where `k` is unknown, the
column wouldn't fully collapse — we'd emit a `call_indirect` and the
truncation cuts above rung 0.  Three rungs in, two emitted as
distinct functions, one as an indirect target.

### What this teaches

- **Suspension fully collapses small examples.**  Bool-flip becomes
  a constant function after inlining; the rise's column reduces to
  one rung.
- **`Hyper Pt Pt` is the right rung type.**  Each rung is "I take a
  continuation and tail-call it" — exactly `Hyper`.
- **The diff-list `InstrRise` is built incrementally.**  Each
  fragment is a tiny `WasmFrag` (LocalGet, Call, etc.); they
  compose via `(^^)` with O(1) cost.
- **Truncation is a discrete decision.**  Either a callee is
  statically known (visible-rung) or it isn't (`call_indirect` +
  table entry).  There's no in-between.
- **Peephole opts wouldn't fire here** (the example is too small),
  but for any non-trivial function the post-emit zipper-pass would
  collapse common idioms.

### Why this is a good v0 target

`Bool` with `T → F; F → T` is:

- The smallest non-trivial `data` declaration.
- Has no parameters, no refinement, no existentials.
- Has Scott codegen already in `Constructor.Scott` (Haskell oracle
  via `runghc`).

So we can: (i) emit a Wasm module for `bool_flip`, (ii) compare
against the Haskell oracle's output, (iii) verify byte-level
correctness on a couple of inputs.  Smallest meaningful integration
test.

## Why motoko's InstrList vindicates the framing

Reading `~/motoko/src/codegen/instrList.ml` cold, you see:

- Diff-list `(^^)` concatenation as the basic op.
- `nop` as identity.
- Reader-of-context (Depth, Region).
- Peephole rules as local rewrites on flat lists.
- Promise-based lazy depth resolution.
- Two backends sharing the substrate.

None of this is motivated in the file by category theory or
hyperfunctions.  It's all engineering decisions made for concrete
reasons (`O(1)` concat, label resolution, two-backend reuse).

But every one of those choices *fits* the `Rise`-algebra framing:

- diff-list `(^^)` = `Monoid (p a a)` for the endo case.
- `nop` = `mempty`.
- Reader context = a profunctor-level state attached to each rung.
- Peephole rules = inner-rise suspensions.
- Promise-based depth = lazy resolution of `KnownRise` levels.
- Two-backend share = same substrate, different `p`-instantiations.

This is the test that the framing is real: the engineering choices
*already made* in motoko's codegen — none informed by the
hyper-rise / (γ) framework — fall out naturally as instances of the
framework's operations.  The framework isn't imposing structure; it's
naming structure that's already there.
