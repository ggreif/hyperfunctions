# Wasm codegen for the constructor — slim architecture

**Status:** vision / architecture sketch.  Revised 2026-05-31 after
the user's calibration that the earlier 7-stage profunctor cascade
was over-stretching `Rise`.

This document supersedes the first-pass version (preserved in git
history at `ebc43a9`).  Key correction: **Wasm is direct-style** (a
stack machine with structured control flow), not CPS.  Forcing a
global CPS pass fights the target.  CPS earns its place *locally*,
inside Scott eliminator scopes where continuations are
compile-time-distinguishable and lower to `br` or `return`.

The honest scope of the rise algebra:

- **For optimisation** (inlining, peephole, indirect-call cuts):
  `Rise` is the right algebra.  Suspension, truncation, and the
  retraction laws all apply directly.
- **For lowering** (IR-to-IR rewriting): each IR wants its *own*
  algebraic shape that fits the IR's purpose.  Not all of them are
  `Γ p Pt Pt`-shaped.

Different layers, different algebras.  All Rise-inspired (column
algebra, named successors, suspension as reasoning) but not all
literally `Rise` instances.

## TL;DR

Three real stages:

1. **Constructor IR** (post-`HypTwr`) **→ Wasm-with-Local-CPS.**
   Direct-style instructions, but Scott-elim scopes carry first-class
   labeled continuations (`local-cont $kT ↦ body`, `dispatch v $arm₁
   …$armN`).  Lowering frontend to backend.
2. **Wasm-with-Local-CPS → Hard Wasm.**  Lower the Local-CPS to
   `block`/`br_table`/`br`/`return`.  Eliminates the only
   non-bytecode-able construct.
3. **Hard Wasm → Bytes.**  Serialise.

Each stage has:

- A typed IR with its own algebraic shape (not necessarily `Γ`).
- An interpreter for testing/validation (semantics contract).
- A lowering pass to the next stage.
- Optimisations expressed as algebraic moves on the layer's shape.

The rise algebra applies *within* layers (instruction-level
suspension on Hard Wasm, function-level suspension on call graphs,
truncation at indirect-call boundaries) but does not span layers —
crossing a layer boundary is a *lowering*, not an algebraic
evolution.

## Per-IR algebraic structures

Each IR layer has its own natural algebra.  Listed below with a
sketch of the shape and what operations make sense.

### Layer A — Constructor IR (post-`HypTwr`)

**Already in tree.**  Concrete representation:
`Constructor.HypTwr.HypTwrVal` (typed value-level AST) plus
`Constructor.Tower = Γ TyView TyView` (the typing tower).

Algebra: a **typing tower** (`Γ TyView TyView`).  The horizontal at
each rung is the type-view; the vertical climbs through kinds.
Operations: `meetTowers`, `kindOf`, `materialize`.

Suitable as the source IR: the frontend produces this directly.

### Layer B — Wasm-with-Local-CPS

**To be designed.**  Structurally a **scope tree** (not a column):
each function's body is a tree of nested scopes, where each scope is
either:

- A sequence of direct-style instructions ending in one of:
  - `return` (back to caller),
  - `br $label` (jump to a higher scope's labeled point),
  - `dispatch scrutinee $arm₁ …$armN` (Scott elim dispatch),
  - or fall through to the parent scope's continuation.
- A `block $label { body }` introducing a labeled scope; the body
  is itself a scope.

Each `dispatch arm` is itself a scope (the continuation's body).

**Why a tree, not a column.**  Scopes nest, and `dispatch` branches.
The shape isn't linear, so the `Γ p a b`-style column doesn't fit
without forcing.  But the *level apparatus* from `KnownRise` carries
over: scopes have depths, `br N` is the N-rung jump.  So:

```haskell
data Scope a where
  Seq    :: [Instr] -> ScopeTail a -> Scope a
  Block  :: Label -> Scope a -> Scope a

data ScopeTail a where
  Return    :: a -> ScopeTail a            -- result
  Br        :: KnownNat n => Proxy n -> ScopeTail a
  Dispatch  :: Scrutinee -> [Scope a] -> ScopeTail a
  FallThru  :: ScopeTail a                  -- implicit continuation
```

This is a **branching cofree-comonad-like tree** with `KnownNat`-
typed back-edges.  Algebra: tree fold/traversal; the `KnownRise`
level apparatus on `br N`.

Suspension is well-defined per-subtree (substitute a subtree for its
collapsed equivalent).  Truncation is `Br $⊤` (or an indirect
dispatch).

This is the Rise-inspired-but-not-Rise layer.  The column has been
generalised to a tree with named back-edges.

### Layer C — Hard Wasm

**To be designed.**  Structurally a **column of instructions per
function**, plus a flat **function table**.  This is exactly motoko's
shape:

```haskell
type WasmFrag = Depth -> Region -> [Instr] -> [Instr]
type InstrRise = Γ WasmFrag [Instr] [Instr]     -- per function
data WasmFunction = WasmFunction
  { sig'      :: FuncType
  , locals    :: [ValueType]
  , bodyRise  :: InstrRise
  }
data WasmModule = WasmModule
  { funcs     :: [WasmFunction]   -- flat list, not a rise
  , funcTable :: Table FuncIdx    -- truncation boundary entries
  , globals, memory, exports :: ...
  }
```

Algebra:

- *Within a function:* the instr-rise `Γ WasmFrag [Instr] [Instr]`.
  Endo-towered (`a = b = [Instr]`), so `Monoid` is automatic;
  `mempty = nop`, `(<>) = (^^)`.  Diff-list with `O(1)` concat.
- *Across functions:* a flat list with a function table for
  indirect calls.  No outer "call rise" at this layer — the call
  graph is implicit in `Call $f` instructions; algebraic
  optimisations like inlining happen *before* this layer (on the
  Wasm-with-Local-CPS scope-tree).

Why no outer-rise here: by the time we're at Hard Wasm, all the
"is this caller's call statically known?" decisions have been
made.  The call graph is just bytes.  The remaining algebraic work
is at the instruction level (peephole), which is the inner rise.

### Layer D — Bytes

A flat byte sequence.  No algebra.  Validation against the Wasm
spec; produce a `.wasm` file.

### Summary of layer algebras

| Layer | IR | Algebra | Rise-shaped? |
|-------|-----|---------|--------------|
| A | Constructor IR + `Tower` | `Γ TyView TyView` (typing tower) | yes |
| B | Wasm-with-Local-CPS | Branching cofree tree + `KnownNat` levels | Rise-inspired, not Rise |
| C | Hard Wasm | `InstrRise = Γ WasmFrag` per function; flat module | yes per-function; no outer |
| D | Bytes | n/a | no |

## Interpreters for each stage

Each IR layer needs an **interpreter** — a semantic function from IR
to runtime result (or to a denotation in some semantic domain).
Interpreters serve three purposes:

1. **Semantics contract.**  An interpreter pins down what each IR
   *means*; lowerings must preserve that meaning.
2. **Differential validation.**  Compile through stages; run the
   interpreter at each stage; results must agree.  Catches lowering
   bugs early.
3. **Debugging / introspection.**  When a Wasm output misbehaves,
   running the interpreter at an earlier layer pinpoints which
   lowering introduced the bug.

### Interpreter A — Constructor IR

Already exists in spirit via `Constructor.Hs` (Haskell codegen
through `runghc`).  Could also build a direct in-memory interpreter
on `HypTwrVal`.

```haskell
interpA :: HypTwrVal m -> Value
```

Where `Value` is the runtime universe (closures, ctors, etc.).

### Interpreter B — Wasm-with-Local-CPS

Custom interpreter that walks the scope tree.  Each `Scope` has:

```haskell
data WasmState = WasmState
  { stack    :: [Value]
  , locals   :: Map LocalIdx Value
  , scope    :: ContextStack       -- nested scopes' labels
  , funcs    :: Map FuncIdx Function
  }

interpB :: Scope a -> WasmState -> (a, WasmState)
-- Scope evaluation:
--   Seq instrs tail -> run instrs, then run tail
--   Block label body -> push label; run body; pop label
--   Tail Return  -> exit function
--   Tail Br n    -> unwind n scopes
--   Tail Dispatch -> pick arm based on scrutinee
```

The `dispatch` semantics: a Scott eliminator selects an arm by
scrutinee shape; the arm's continuation runs in the current scope.

### Interpreter C — Hard Wasm

The standard Wasm spec defines this.  Either:

- Use an existing Wasm interpreter (Haskell's `wasm` package, or
  shell out to `wasm3` / Wasmer / wasmtime).
- Write a minimal in-memory interpreter handling the subset we
  emit.

The latter is probably worth it for the v0: small instruction
subset, easy to validate against B's interpreter.

```haskell
interpC :: WasmModule -> ImportEnv -> [Value] -> [Value]
```

### Interpreter D — Bytes

Run the actual bytes through `wasmtime` or `wasm3`.

### Validation chain

```
interpA(constructor IR)        ──┐
                                  ├─ should all agree on observable I/O
interpB(lower to Wasm-Local-CPS) ─┤
                                  │
interpC(lower to Hard Wasm)    ──┤
                                  │
interpD(serialise to bytes)    ──┘
```

Each lowering is a *refinement*: it makes some semantic choices
concrete (continuation shapes, instruction sequences, byte
representation) but cannot change observable behaviour.  Equivalence
of interpreters is the lowering's correctness condition.

## Where the rise algebra still applies

Three real places where `Rise` (or close-cousin column algebras) earn
their keep:

### 1. Inlining as suspension on the function call graph (pre-Layer-C)

When lowering A→B or doing optimisations within B, the *call
graph* of the program is implicitly a rise: each function is a
rung, each direct call is a vertical edge.  Inlining a known
callee = `retreat (collapse [caller, callee], rest)` — fuse two
rungs.

This happens **at the Wasm-with-Local-CPS layer** (after frontend
lowering, before Hard Wasm).  Once we're at Hard Wasm, all
inlining decisions have been made; the call graph is just `Call
$f` instructions.

The function-rise isn't a separate data structure in the IR — it's
*derived* from the call graph.  Inlining mutates the layer-B IR
according to suspension semantics, but the IR itself stores
functions in a `Map FuncIdx Function`, not as a `Γ`.

### 2. Peephole opts as instruction-rise suspension (within Layer C)

The `InstrRise = Γ WasmFrag [Instr] [Instr]` per function is a
genuine `Rise` instance.  Peephole rules are local rewrites:

- `LocalSet n :: LocalGet n :: rest → LocalTee n :: rest`
- `Const _ :: Drop :: rest → rest`
- `Const c :: Const c' :: Binary And :: rest → Const (c.&.c') :: rest`

Each rule is a one-rung-pair suspension.  The whole `optimize` pass
in motoko's `instrList.ml` is an iterated suspension cascade.

This is the cleanest application of the rise algebra: the rules
ARE algebraic rewrites with the suspension shape, no stretching.

### 3. Truncation at indirect-call boundaries

When the codegen cannot statically resolve a call (its callee isn't
known at compile time), it emits `call_indirect` against a function-
table entry.  In rise vocabulary: the call-graph rise *truncates*
at that point.

This is a categorical decision (resolved vs not), not a continuous
spectrum.  The function table is the runtime data structure that
carries the truncated content.

### 4. `KnownRise` for `br N` levels (in Layer B)

The scope-tree at layer B has nested scopes with depths.  `br N`
addresses the N-th-outer scope.  This is `KnownRise`'s `succ`
applied N times on the level type.

**This is where `KnownRise` first earns its keep operationally** —
it types the back-edges in the scope tree.  Compile-time guarantee
that every `br N` has a valid target.

```haskell
data ScopeTail (l :: Nat) a where
  Return :: a -> ScopeTail l a
  Br     :: (n <= l) => Proxy n -> ScopeTail l a   -- typed
  Dispatch :: Scrutinee -> [Scope l a] -> ScopeTail l a
```

The `n <= l` constraint statically enforces that the back-edge is
in-scope.  Wasm's validator catches this at validation time;
`KnownRise`-typed scopes catch it at compile time.

## Concrete `p` choices — diff-list-of-Wasm-fragments

For Layer C's per-function inner rise, the profunctor is motoko's
`InstrList.t`:

```ocaml
type t = int32 -> Wasm.Source.region -> instr list -> instr list
```

Translating to Haskell:

```haskell
type Depth   = Int32
type Region  = Wasm.Source.Region
type WasmFrag = Depth -> Region -> [Instr] -> [Instr]
-- i.e., Reader (Depth, Region) (Endo [Instr])
```

Properties:

- **Endo on `[Instr]`** (`a = b = [Instr]`).  `Monoid (WasmFrag)`
  is automatic; `mempty = nop`, `(<>) = (^^)`.
- **`O(1)` concat** via diff-list shape.  Each `(^^)` is function
  composition.
- **Reader of (Depth, Region)** — depth threads block-depth context
  for `br N`; region threads source-position for DWARF.

This is the proven motoko shape, transplanted.  Use it verbatim.

## Why structured control flow is `KnownRise`-shaped

Wasm's structured control flow (`block`, `loop`, `if`, `br N`,
`br_table`) is the textbook `KnownRise`:

- Entering a `block`/`loop` pushes a level (the type's `succ`).
- Leaving pops.
- `Br N` targets the N-th enclosing scope — i.e., `iterate N stepUp
  current`.

Motoko's `int32` depth labels are the level coordinates.  Motoko's
`Lib.Promise` mechanism for lazy depth resolution is what
`KnownRise`'s type-level levels would replace at compile time.

Per the user's calibration: this is where Local-CPS scopes lower to.
A `dispatch` becomes `br_table` over labels; a `local-cont` becomes
a labeled `block`; an arm-tail `br $kT` becomes `br N` for the
appropriate N (computed at lowering time from the depth-of-`$kT`
in the scope tree).

## Lowering A → B — frontend to Wasm-with-Local-CPS

This is the largest single transformation.  Input is a typed
`HypTwrVal`; output is a Wasm-with-Local-CPS scope tree per function.

**Steps within the lowering:**

1. **Closure-convert.**  Free variables → explicit captures.
   Lambdas become `(funcref, capture-ptr)` pairs.  Each lambda
   becomes a Wasm function in the output module.
2. **Scott-emit.**  `data` declarations produce ctor functions and
   their Scott eliminators.  Each ctor packages its args into a
   closure; the eliminator dispatches by reaching into the closure
   shape.  (Standard Scott encoding, already done in
   `Constructor.Scott`.)
3. **Local-CPS-emit.**  `case e { ... }` becomes a `block` scope
   containing a `dispatch` of the scrutinee against the arm
   continuations.  Each arm is a `local-cont` (a scope).
4. **Direct-style instructions for the rest.**  Arithmetic, locals,
   calls — all direct.

The "ANF" idea from the earlier draft collapses into step 4: by
emitting one instruction per IR sub-expression, the result is
already in ANF-shaped form.  No separate ANF pass.

## Lowering B → C — Local-CPS to Hard Wasm

The structural rewrite the user identified.  For each scope:

- `Seq instrs (Return result)` → emit instrs, push result, `return`.
- `Seq instrs (Br N)` → emit instrs, `br N`.
- `Seq instrs FallThru` → emit instrs (no terminator).
- `Block $label body` → emit `block $type` … `end`; inside is the
  body's lowering.
- `Seq instrs (Dispatch v arms)` →
  - Push the value `v`.
  - `br_table [label_arm₁, label_arm₂, ...]`, where each `label_armᵢ`
    is the depth of the i-th arm's scope in the surrounding block
    structure.
  - Below the `br_table`, emit each arm's scope in sequence with
    a `br $exit` at the end (where `$exit` is the common
    continuation).

**Key invariant:** every `Br N` in layer B must have N ≤ enclosing-
scope-depth.  Compile-time check (per `KnownRise` typing) catches
violations.

**Tail-position dispatch becomes `return`.**  If a `dispatch`'s arm
is in tail position (the function's outermost scope), each arm's
`br` becomes `return` instead.  This is the `return_call` /
`return_call_indirect` analog at the structured-CF level.

## Lowering C → D — Hard Wasm to bytes

Standard Wasm spec.  Probably use an existing serialiser (the
`wasm` Haskell package has one).  No interesting algebra here.

## Worked example — `data Bool⋮ { T⋮; F⋮ }` revisited

Same example as before, but expressed in the slim architecture.
Source:

```
data Bool⋮ { T⋮; F⋮ }
case T { T -> F; F -> T }    -- bool-flip
```

### Layer A — Constructor IR

`HypTwrVal` carries:

- `Bool : TyView`
- `T : Bool`, `F : Bool`
- the case expression with arms `T→F` and `F→T`

The typing tower (`Γ TyView TyView`) carries the kind annotations.

### Layer B — Wasm-with-Local-CPS

After lowering A→B:

```
;; ctor functions emitted (closures)
function $t_ctor   = Closure { funcref=$t_body, captures=[] }
function $f_ctor   = Closure { funcref=$f_body, captures=[] }

;; bool_flip's body: a scope tree
function $bool_flip = scope:
  Seq [LocalGet 0    -- k (the outer continuation)
      ]
      (Block $exit (
        Seq []
          (Dispatch (call $t_ctor)         -- the scrutinee
            [ scope: Seq [] (Br $exit       -- arm_T → F (via tail-call k)
                              after running f_ctor)
            , scope: Seq [] (Br $exit       -- arm_F → T
                              after running t_ctor)
            ])))
```

(Sketchy syntax; the real IR would be a proper tree value.)

The key point: `dispatch` has labeled-continuation arms, not
closures.  Local-CPS is operational.

### Layer C — Hard Wasm

Lower B→C: `dispatch` → `br_table`; arms become labeled blocks.

```
;; bool_flip function
(func $bool_flip (param $k funcref) (result ...)
  block $exit (result i32)
    block $arm_F
      block $arm_T
        ;; compute scrutinee (T or F)
        call $t_ctor
        ;; dispatch: ctor tag → arm label
        br_table $arm_T $arm_F
      end ;; arm_T
      ;; arm_T body: compute F, return
      call $f_ctor
      br $exit
    end ;; arm_F
    ;; arm_F body: compute T, return
    call $t_ctor
    br $exit
  end ;; exit
  ;; tail-call k with the result
  local.get $k
  return_call_indirect (...)
)
```

This is the natural Wasm shape.  No closures for the arm
continuations; just `block`s.  After peephole opts (the
`InstrRise` suspension cascade), the function would shrink further.

### Layer D — Bytes

Serialise.

### Note on the example's collapsibility

In the earlier draft I claimed the example collapses to "~6 bytes"
after suspension.  That's still right *in spirit* — full inlining
collapses ctor calls into the dispatching site — but the right
place for that collapse is **at layer B**, not via a "profunctor
evolution at layer 5."  At layer B, the optimisation is: inline
the ctor's scope into the dispatching arm, then the `br_table`
becomes a no-op (single arm always taken), then the `block`s
collapse.  Each step is an algebraic move on the scope tree —
not a Rise suspension, but a tree-rewrite with similar laws.

## What the rewrite kept vs trimmed

**Kept:**

- Algebraic vocabulary for code transformations (inlining,
  peephole, truncation).
- `WasmFrag` diff-list as the per-function inner-rise `p`.
- `KnownRise`-typed `br N` as the natural application of the
  level-aware substrate.
- Function-table boundary as the truncation apparatus.
- Two-backend share (motoko's classical vs enhanced) as
  precedent for substrate reuse.
- Peephole opts as instruction-rise suspension cascade.
- Worked example (refactored to direct-style).

**Trimmed:**

- The 7-stage profunctor cascade (IR → ANF → CPS → Closure → Scott
  → Direct.Wasm → Tabled.Wasm → Final).  Most stages weren't real
  partitions.
- Global CPS pass.  Wasm is direct-style; global CPS fights the
  target.
- ANF as a separate stage.  Direct-style instruction emission is
  already ANF-shaped.
- Closure-conversion as a separate stage.  It's a sub-step of
  layer-A→B lowering.
- "Everything is `Γ p Pt Pt`" overselling.  Each layer wants its
  own algebra fitted to its purpose.

**Lesson:** the rise algebra is right for *optimisation*
(suspension, truncation, peephole) but not for *lowering* (which is
structural rewriting across IRs).  Optimisation preserves IR
structure and refines content; lowering changes the IR shape
itself.  Conflating them was the over-stretch.

## Concrete starting plan (revised, 6 steps)

1. **Define layer B's IR** — the scope tree with `dispatch`,
   `local-cont`, `Br`, `Block`, direct-style `Seq` of instructions.
   Plus the function-table apparatus.
2. **Build interpreter B** — walks the scope tree per the semantics
   sketched above.  Use to validate the A→B lowering.
3. **Lower A → B** — closure-convert, Scott-emit, Local-CPS-emit,
   direct-style for the rest.  Run interpreter B; verify against
   the existing Haskell-oracle (`Constructor.Hs`).
4. **Define layer C's IR** — Hard Wasm.  `WasmFunction` +
   `InstrRise = Γ WasmFrag` per body + `WasmModule` with function
   table.
5. **Build interpreter C** — small subset of Wasm; validate against
   B.  Or shell out to `wasmtime`.
6. **Lower B → C** — structural rewrite per the spec above.  Add
   peephole opts as `InstrRise → InstrRise` suspension rules (or,
   motoko-style, a post-materialisation zipper pass — proven for
   v0).

Layer D (bytes) is just serialisation; use an existing library.

`KnownRise` lands at step 1 (typing layer-B scopes) and is exercised
in step 6 (lowering `Br N` to Wasm `br N`).

## Connection to existing constructor code

- `Constructor.HyperRise` — substrate for the per-function inner
  rise at layer C.  `type InstrRise = Γ WasmFrag [Instr] [Instr]`.
- `Constructor.Tower` — the typing tower at layer A.
  `type Tower = Γ TyView TyView`.  Already in tree.
- `Constructor.Scott` — Scott codegen to Haskell, current
  oracle.  Will be the differential-validation target for layer B's
  interpreter.
- `Constructor.HypTwr` — produces layer A's IR.

To be added:

- `Constructor.Wasm.LCPS` — layer B's scope-tree IR + interpreter.
- `Constructor.Wasm.Hard` — layer C's IR + interpreter.
- `Constructor.Wasm.Frag` — the `WasmFrag` diff-list profunctor.
- `Constructor.Wasm.Lower` — A→B and B→C lowerings.
- `Constructor.Wasm.Peephole` — instruction-rise suspension rules.
- `Constructor.Wasm.Bytes` — D-layer serialiser (or wrap an
  existing library).

## References

- `Constructor.HyperRise` (in `~/hyperfunctions/constructor/src/`) —
  the `Rise` substrate.
- `~/hyperfunctions/constructor/PLAN.md` — "Hyper-rise" + "Absolute
  version: `KnownRise`" sections.
- Git-note on `38d9ed6` in `~/hyperfunctions` — calling-convention-
  as-(γ) framing (still load-bearing for the optimisation algebra,
  even after the over-stretch correction).
- `~/opetopic/.claude/plans/opetope-as-rise.md` — parallel
  polynomial-functor encoding for opetopes.
- `~/motoko/src/codegen/instrList.ml` — the `WasmFrag` shape this
  plan adopts verbatim.
- Wasm spec, particularly:
  - Tail-call extension (`return_call`, `return_call_indirect`).
  - Structured control flow (`block`, `loop`, `if`, `br`,
    `br_table`).

## Lessons learned (the prior over-stretch)

For posterity — the calibration arc that got us here:

- **First-pass framing (commit `ebc43a9`):** a 7-stage profunctor
  cascade IR → ANF → CPS → Closure → Scott → Direct → Tabled →
  Final, with each step a `pₖ ~~~> pₖ₊₁` profunctor evolution.
  Concrete `p` choices (`WasmFrag`), two granularity levels
  (function-rise + instr-rise), Wasm-instruction → rise-op map.
- **The user's calibration:** Wasm is direct-style; global CPS is
  wrong; ANF is too close to Wasm to be a separate stage; CPS
  belongs *locally* in Scott-elim scopes where continuations are
  compile-time-distinguishable.
- **What survived:** the algebraic-optimisation claims (suspension,
  peephole, truncation, `KnownRise` for control flow), the
  concrete diff-list `p`, the worked example's spirit.
- **What was trimmed:** the 7-stage cascade, global CPS, ANF as a
  separate stage, "everything is `Γ p Pt Pt`."
- **The principle now explicit:** Rise applies to *optimisation*
  (within-IR algebra), not to *lowering* (across-IR rewriting).
  Different layers want different algebras fitted to their
  purpose.  All Rise-inspired in vocabulary (column algebra, named
  successors, suspension), but the literal `Γ p a b` shape is only
  one of several IR-fitting algebras.

The earlier draft is preserved in git history at `ebc43a9` for
anyone who wants to trace the calibration.
