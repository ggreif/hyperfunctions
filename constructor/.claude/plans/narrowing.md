# Narrowing — type-level computation via Hyper/LogicT search

**Status:** **Phases A–D landed 2026-06-01.**  Original sketch
2026-05-31; implementation in commits `04eef5c` (slide-down) →
`f89dd6f` (interpreter) → `df54e4a` (bridge) → `5194a31`
(narrowing).  This document records the original vision and now
also tracks what's done vs what's still ahead.

## Implementation status — at a glance

| Phase | Mechanism | Status | Commit | Tests |
|---|---|---|---|---|
| **A** | Slide-down `TyDeferV` on `TyUnbound` | ✅ done | `04eef5c` | 2 in GadtSpec |
| **B** | Value-level interpreter (`Constructor.Interp`) | ✅ done | `f89dd6f` | 11 in InterpSpec |
| **C** | Demote / interp / promote bridge at meet sites | ✅ done | `df54e4a` | 1 end-to-end in GadtSpec |
| **D-min** | Narrowing on stuck meta args (nullary ctors) | ✅ done | `5194a31` | 1 end-to-end in GadtSpec |
| **D-full** | Unary/multi-arg narrowing (fresh path-derived sub-meta) | ✅ done | `951bfdf` | 1 end-to-end in GadtSpec |
| **D-disj** | All-branches search; candidates from the fn's case arms | ✅ done | (this commit) | two-arm `isS` in GadtSpec |
| **Hyper-LogicT** | Replace `[]`-list bag with Kidney/Wu's substrate | pending | — | — |
| Layer 3 | User-supplied equational theorems as rewrites | pending | — | — |
| Layer 4-Lite | Homogeneous-type essence + Presburger decision | pending | — | — |
| Layer 4-Full | Automatic IH reuse via structural recursion | pending | — | — |

**End-to-end demonstration** (commit `5194a31`):

```
data Nat⋮ { Z⋮; S Nat⋮ };
let pickZ = \n -> case n { Z -> Z };
data Wit (n : Nat) : *0 { W : pickZ n -> Wit n };
let rt = W Z
```

`W Z`'s elaboration requires `pickZ ?n ≡ Z` where `?n` is fresh.
Standard meet fails (TyMismatch).  Phase D's narrowing fallback
case-splits `?n` on the singleton type `Z`'s only inhabitant
(`Z` itself), reduces `pickZ Z = Z` via the bridge, meets cleanly.
Refinement `?n := Z`.

### D-full — unary/multi-arg narrowing

```
data Nat⋮ { Z⋮; S Nat⋮ };
data Bool⋮ { T⋮; F⋮ };
let sT = \n -> case n { S m -> T };
data Wit (n : Nat) : *0 { W : sT n -> Wit n };
let rt = W T
```

`W T` forces `sT ?n ≡ T`.  Narrowing reads `sT`'s sole arm pattern
`S m` (from its `Expr` body in `Globals`), mints one **path-derived**
sub-meta `?m` (its `MetaId` extends `?n`'s paths with `PsCtorAppArg 0`
— no gensym), refines `?n := S ?m`, and reduces `sT (S ?m) = T`
because the arm body ignores `m`.  The sub-meta stays legitimately
free; the ground result `T` meets the LHS.

### D-disj — disjunctive search; candidates from the function's arms

The enumeration source is the **deferred function's own `case`
arms**, not the argument's declared type:

```
data Nat⋮ { Z⋮; S Nat⋮ };  data Bool⋮ { T⋮; F⋮ };
let isS = \n -> case n { Z -> F; S m -> T };
data Wit (n : Nat) : *0 { W : isS n -> Wit n };
let rt = W T
```

`W T` forces `isS ?n ≡ T`.  `isS`'s arms are `{Z, S}`, so narrowing
tries both: `?n := Z` gives `isS Z = F` (meet with `T` fails) and
`?n := S ?m` gives `isS (S ?m) = T` (meet succeeds, first wins).
Refinement `?n := S ?m`.

This is the candidate set that could *possibly* make the application
reduce — any ctor not in the arms hits no arm and goes stuck — so it
is both **precise** (no wasted branches) and **disjunctive** (one
branch per arm, the list monad as the bag).  It also makes the
multi-arm case fall out for free.

Mechanism:

- **Candidate source** (`armCtors`): read `fname`'s body from
  `Globals`, peel its lambda binders, and if the body is
  `case xⱼ { … }` collect each arm pattern's `(ctor, arity)` for
  argument position *j*.  No type lookup, no side table.
- **Sub-meta minting** (`narrowArg`): for an arity-*k* arm pattern,
  build a `TyAppV` spine over *k* path-derived sub-metas.  Nullary
  (*k*=0) gives a bare `TyConV`.
- **Free sub-metas through the bridge**: `demote` carries a free meta
  as `VStuck (SMeta mid)` (holding the `MetaId` directly — paths
  intact); `EMeta`/`valueToExpr` round-trip it through `interp`.  An
  arm body that *uses* the sub-meta yields a stuck result → `promote`
  fails → that candidate is rejected (conservative + correct).

**Resolved.**  The earlier D-full draft sourced candidates from the
argument's *declared type*, which a two-arm function leaves as an
unresolved meta (per-arm Subst-fork commits no agreed parameter
refinement — git-note `0aa6e9d`).  Reading the arms instead sidesteps
that entirely: a function that matches on `S` *tells us* to try `S`,
regardless of how its parameter's type inferred.  The type-sourced
path (`narrowOnce`'s old `dataCtors`/`fnTypes` args, `extractDataCtors`,
`hypTwrEnvDataCtors`) is now vestigial — removal is a follow-up
cleanup commit.

---

## Original 2026-05-31 sketch (preserved below for context)

**Status:** vision / architecture sketch.  Captures the discussion arc
2026-05-31 around type-level reasoning beyond pure refinement.  The
trigger was `Refl on Eq (add a b) (add' a b)` — a propositional
equality requiring type-level evaluation of value-level definitions
with stuck metavariables.

## The motivating example

Two definitions of natural-number addition:

```
add  (Z)   m = m
add  (S n) m = S (add n m)              -- right fold

add' (Z)   m = m
add' (S n) m = add' n (S m)             -- left-accumulator
```

Both compute the same function (commutativity of addition).  A
witness should be expressible:

```
data Eq (a : Nat) (b : Nat) : *0 { Refl : Eq a a };
let addEq : ∀ a b. Eq (add a b) (add' a b)
addEq = Refl
```

The current constructor language *rejects* this — `add a b` is not a
type expression because `add` is a value-level let-binding, not a
type constructor.  Even with the proposed promotion (next section),
the two sides don't structurally unify; they require *computation*
under stuck metavariables `a, b`.

This is the territory of dependent type checking with general
recursion at the type level.  Doable, but requires three distinct
mechanisms.

## Layer 1 — Demote / Interpret / Promote via `⋮`

**Status: ✅ landed (commits A `04eef5c`, B `f89dd6f`, C `df54e4a`).**

The `⋮` self-tower annotation is the bridge.  Whenever a function's
signature has all-`⋮`-typed slots (both args and result), the
function lifts to type level by:

1. **Demote** the type-level arguments through the `⋮`-iso to their
   value-level equivalents.
2. **Interpret** the value-level call (run the IR's beta-reduction
   engine to a normal form).
3. **Promote** the value-level result back through the `⋮`-iso to
   the type level.

Mechanically the `⋮`-iso is *almost identity* on the representational
shape — the same syntactic node serves as value-level expression and
type-level expression once self-tower has collapsed the column.

Worked example, `Eq Z (add Z Z)`:

- Demote `Z, Z` (type level) → `Z, Z` (value level).
- Interpret `add Z Z` → `Z` (one case-arm dispatch).
- Promote `Z` (value level) → `Z` (type level).
- Now `Eq Z (add Z Z) ≡ Eq Z Z`, Refl applies, ✓.

This is decidable and terminating when all arguments are fully
reduced to ctor normal forms.  Fails when args contain metas: the
interpreter blocks on case-of, can't proceed.

### What Layer 1 implements

- A value-level interpreter for the IR (new carrier — `Interp`?).
- A predicate "is this type expression all-`⋮`-typed and
  fully-evaluated?"
- The demote/promote glue (mostly representational; the `⋮` collapse
  makes it trivial in syntax).

Scope: ~couple hundred lines of code.  Self-contained.  Unlocks the
fragment of type equalities reachable by pure normalisation of
concrete-arg expressions.

## Layer 2 — Narrowing

**Status: ✅ minimal subset landed (commit `5194a31`).**
**Remaining: multi-arg / unary-ctor cases (fresh sub-meta gen);
disjunctive all-branches search (currently first-wins); Hyper-
LogicT substrate (currently plain `[]` list-monad bag).**

When Layer 1's interpreter is stuck on a meta, **case-split the
meta** and recurse on each ctor case.  This is the Ωmega narrowing
move (and the classical logic-programming move).

For `Eq Z (add Z m)` (where `m` is a fresh meta of type `Nat`):

- Interpreter blocks: `add Z m` reduces to `m` (Z-arm) only if the
  case-of can fire.  With `add`'s second arg being `m`, *the first
  arg is `Z`* — concrete — so reduction *does* fire: `add Z m → m`.
  No narrowing needed.

For `Eq Z (add n Z)`:

- Interpreter blocks: `add n Z` requires inspecting `n`'s head ctor
  to choose a case-arm.  Narrow:
  - `n := Z`: `add Z Z → Z`; goal `Eq Z Z`, ✓.
  - `n := S k` (fresh k): `add (S k) Z → S (add k Z)`; goal
    `Eq Z (S (add k Z))`.  Heads `Z` vs `S` differ — fail.
- Narrowing returns one verdict per branch.  The overall result is a
  *disjunction* of refined substitutions: "either `n = Z` or fail."

For our motivating example `Eq (add a b) (add' a b)`:

- Stuck on `a`'s ctor.  Narrow:
  - `a := Z`: both sides reduce to `b`.  Goal `Eq b b`, ✓.
  - `a := S n`: LHS = `S (add n b)`; RHS = `add' n (S b)`.  Goal
    `Eq (S (add n b)) (add' n (S b))`.  Heads `S` vs `add'` — differ,
    but the RHS isn't fully reduced; need to apply IH or recurse.

Naive narrowing on the `a := S n` branch case-splits `n`, then
`m`, etc. — infinite descent without a stopping rule.  Pure
narrowing handles a useful fragment (anything decidable by finite
case-split) but not inductively-defined equalities.

### What Layer 2 implements

- A `meet` extension that catches "stuck on head meta" and
  case-splits.
- Disjunctive result handling (each case-split branch can succeed,
  fail, or recurse).
- A search-engine substrate — *LogicT-over-Hyper* is the natural fit
  (see "Hyper / LogicT connection" below).

Scope: substantial — extends the unification core.  But each
new case-split is one bounded action on the search column.

## Layer 3 — Equational theorems (Ωmega style)

**Status: ⏳ pending.**  No user-supplied theorem mechanism yet;
theorem-driven rewriting awaits demand from a concrete proof
obligation.

When Layer 2 hits an infinite case-split tree, **the user supplies a
theorem** that the narrowing engine uses as a rewrite rule.

```
theorem add_swap : ∀ a b. add a (S b) = S (add a b)
theorem add_eq   : ∀ a b. add a b = add' a b
```

During narrowing, if the current goal matches a theorem's LHS (with
fresh metas), the engine *rewrites* to the RHS and continues.
Theorems short-circuit case-split trees that would otherwise diverge.

For our example with both theorems registered:

- `Eq (add a b) (add' a b)` directly matches `add_eq`'s LHS.
  Apply: rewrite `add' a b → add a b`; subgoal becomes `Eq (add a b)
  (add a b)`, refl ✓.  (Or skip the rewrite and case-split on `a`;
  either path closes.)

### What Layer 3 implements

- Parser support for `theorem name : ∀ ... . lhs = rhs`.
- An env extension recording theorems.
- A rewrite engine: pattern-match goal against theorem LHS, apply
  substitution, replace with RHS.
- Verification of theorems is **deferred** — either trusted axioms
  (user asserts; system trusts) or a separate proof-check pass.

Scope: ~1-2 weeks.  Self-contained extension on top of Layer 2.

## Layer 4 — Automatic induction-hypothesis reuse

**Status: ⏳ pending.**  Requires termination order + active-goal
tracking + IH-equation matcher — the technically deepest piece.
Most-distant-future of the plan; possibly subsumed by Layer 4-Lite
on the homogeneous fragment.

The killer feature: detect when a recursive subgoal is "the same
equation at a structurally smaller meta" and close it by IH-fiat.

For `add a b = add' a b`, narrowing on `a := S n` produces subgoal
`S (add n b) = add' n (S b)`.  Apply IH on `n` (which is structurally
smaller than `S n`): rewrites `add' n (S b)` to `add n (S b)`.
Subgoal becomes `S (add n b) = add n (S b)` — an auxiliary lemma.

Sub-narrowing on `n` yields the auxiliary lemma's base case:
`S (add Z b) = add Z (S b)`, reduces to `S b = S b`, ✓.  The
inductive step uses *its* IH on `m`, reduces mechanically.

**Both the main theorem AND the auxiliary lemma close by:**
1. Case-split on the recursion arg.
2. Mechanical β-reduction in each branch.
3. IH-application at structurally smaller args.

The ONE place creative input is needed: the base-case equation
`S b = S b`, which is trivially reflexive after reduction.

This is the moral of the structural alignment of `add` and `add'`:
both peel the first argument the same way, so the inductive cases
automate.  When functions don't align, more auxiliary lemmas are
needed — but the engine can still try (and fail) automatically.

### What Layer 4 implements

- A termination order on metas (structural recursion).
- An "active goal" stack tracking equations under proof.
- An IH-stop: when current subgoal matches an active goal with all
  metas mapped to structurally-smaller terms, close.
- Standard guards against unsoundness (the IH applies only when args
  genuinely shrink).

Scope: 2-4 weeks.  The technically interesting one.

## Layer 4-Lite — Homogeneous types and Presburger reduction

**Status: ⏳ pending.**  Essence-extraction + Cooper's-algorithm
port not yet implemented.  Conjectured to be ~2 weeks of work and
to cover an enormous practical fragment (commutativity,
associativity, identity, monus, min/max).

A substantial subset of Layer 4's work is unnecessary when the data
type is **one-dimensional homogeneous** in the sense of Nat.  For
that fragment, equational reasoning collapses to **Presburger
arithmetic**, which is a standard decidable theory with off-the-
shelf decision procedures.  This makes the layer cheaper to
implement than Layer 4-Full *and* gets implemented earlier in the
order (between Layers 2 and 3).

### The homogeneity argument

No sharpened annotation needed.  A `⋮`-typed data declaration is
**one-dimensional homogeneous** iff its ctor signature reduces to:

- **a single ⋮ seed (0-cell)**: exactly one ctor with *no*
  recursive position in the declared type.
- **a single ⋮ generator (1-cell)**: exactly one ctor with
  *exactly one* recursive position in the declared type.

A purely structural check on the declaration.  `Nat⋮` matches:
`Z : Nat` is the seed (0-cell, no recursive position), `S : Nat ->
Nat` is the generator (1-cell, one recursive position).  Each
Nat-value is a finite path of 1-cell generator applications
terminating at the 0-cell seed.

Failure modes ruled out by the cell-count:

- **Two seeds**: `data Bool⋮ { T : Bool; F : Bool }` — finite
  enumeration, not Nat-shaped.
- **Two generators**: `data Bin { Nil : Bin; L : Bin -> Bin; R : Bin
  -> Bin }` — each value records a distinguishable L/R sequence;
  the generators are *not* interchangeable.
- **Branching generator (arity ≥ 2)**: `data Tree { Leaf : Tree;
  Node : Tree -> Tree -> Tree }` — two recursive positions per
  ctor; binary-branching, two-dimensional.

The "1 seed + 1 generator (arity 1)" pattern is exactly what makes
every value characterisable by *one natural number*: the count of
generator applications between value and seed.  All generator
applications are indistinguishable (the cell-count says there's only
one of them; positional information collapses), so per-occurrence
identity vanishes.  This is the structural fact behind "only the
length counts."

For such types, an n-ary function `f : T^n → T` is determined by
its **length-arithmetic essence**: a function `g : ℕⁿ → ℕ` on
the natural-number lengths.  Two functions are equal iff their
essences agree as arithmetic functions.

The reduction:

| Equation on Nat-functions | Arithmetic essence | Decidable? |
|---|---|---|
| `add a b = add b a` (commutativity) | `a + b = b + a` | trivially |
| `add a (add b c) = add (add a b) c` (associativity) | `a + (b + c) = (a + b) + c` | trivially |
| `add a Z = a` (right-identity) | `a + 0 = a` | trivially |
| `add a b = add' a b` (left vs right fold) | `a + b = a + b` after essence-extraction | trivially |
| `monus a a = Z` | `max(0, a - a) = 0` | yes (Presburger) |
| `monus (add a b) b = a` | `max(0, (a + b) - b) = a` | yes (Presburger) |
| `min a b ≤ a` | linear order on ℕ | yes (Presburger) |

All of these collapse to **Presburger arithmetic** — the first-order
theory of ⟨ℕ, 0, S, +, ≤⟩.  Presburger is decidable in
deterministic worst-case doubly-exponential time, polynomial in
practice for typical-sized formulas.  Cooper's algorithm and the
Omega Test are the classical decision procedures; either ports to
~few hundred lines of Haskell.

### The pipeline this implies

1. **Detect homogeneity** of a type from its declaration.
   `Nat⋮ { Z : Nat; S : Nat -> Nat }` matches the pattern; the
   typer flags the type as Presburger-eligible.
2. **Extract arithmetic essence** of each function over a
   homogeneous type.  For structural recursion
   `f Z = e₀; f (S n) = e_step`, the essence is a recurrence:
   - Base case essence: a Presburger expression in the remaining
     args (or constants).
   - Inductive case essence: a Presburger expression in the
     remaining args + `essence(n)` (the IH applied symbolically).
   - Resolve recurrence to closed form.  For linear recurrences
     this is mechanical (substitution + accumulation).
3. **Decide equality** in Presburger via Cooper's algorithm or
   the Omega Test.  Standard.

Worked example, `add` vs `add'`:

- `add`: `add Z m = m`; `add (S n) m = S (add n m)`.
  - Base: essence(Z, m) = m.
  - Step: essence(S n, m) = 1 + essence(n, m).
  - Closed form: essence(a, b) = a + b.  ✓ (linear in both args)
- `add'`: `add' Z m = m`; `add' (S n) m = add' n (S m)`.
  - Base: essence(Z, m) = m.
  - Step: essence(S n, m) = essence(n, 1 + m).
  - Closed form: essence(a, b) = a + b.  (Accumulator unwinds to
    the same linear expression.)

Both essences are `a + b`.  Equal in Presburger trivially.  No
case-split, no IH; just essence-extraction + decision.

### Where multiplication enters

The boundary is **linear vs nonlinear** on ℕ.

- **Linear (Presburger)**: `+`, `-`, `min`, `max`, integer
  constants, `≤`, `=`.  Everything expressible from these.
- **Nonlinear**: `×`, `^`, division, modulo.  Less decidable;
  Presburger doesn't cover.

For Nat-functions:

- `add`, `monus`, `min`, `max`, `pred`, `succ` → linear essence
  → Layer 4-Lite handles.
- `mul`, `pow` → nonlinear essence → falls back to Layer 3
  (user-supplied theorems) or Layer 4-Full (IH-stop).

The practical Nat fragment is overwhelmingly linear.  Multiplication
appears, but its commutativity and associativity are *bilinear*
identities with their own (decidable) decision procedures.  The
truly hard nonlinear arithmetic on ℕ (full Diophantine reasoning)
is rare in everyday code.

### Beyond Nat

The homogeneity criterion lifts to other types:

- **`List a` for trivial `a` (e.g., Unit)**: identical to Nat.
  Same theory.
- **`List a` for non-trivial `a`**: length-arithmetic on the spine
  plus element-arithmetic per position.  Decidable if element
  arithmetic is — extension of Presburger with element-theory
  oracles.
- **`Vec n a`**: length is known at type level; many properties
  decide trivially.
- **Bit strings / finite words**: similar to List, indexed by
  alphabet size.

Two-dimensional / branching types (`Tree`, rose trees) escape
Layer 4-Lite.  Equational reasoning over them needs essences that
are *tuples* of arithmetic expressions (one per subtree
position), or full Layer 4-Full IH-stop machinery, or
user-supplied theorems.

### Conservation-of-ctors as a sanity check

The essence extraction relies on functions being **conservative**
in their ctor usage: no `S` created from thin air, no `S`
destroyed.  A syntactic check on function bodies:

- `add (S n) m = S (add n m)` — peels one `S` from input, emits
  one `S` in result.  Net zero.  ✓
- `add' (S n) m = add' n (S m)` — peels one `S` from arg 1,
  pushes to arg 2.  Net zero across args.  ✓
- A hypothetical `bad (S n) m = add n m` — peels but doesn't
  re-emit.  NOT conservative; produces a result shorter by one.
  Still a valid function; just *not* equal to `add` under Layer
  4-Lite.

The conservation check is structural; it's part of essence
extraction (a function that doesn't conserve will produce an
essence that captures the "loss" or "gain" as an arithmetic
constant).

### Rise / suspension reading

Layer 4-Lite is the **suspension of a recursive function into its
arithmetic essence**.  The value-level recursion is the column;
suspending it collapses the column into one named horizontal cell
(the Presburger formula).  Equality on the original function
reduces to equality on the suspended essence.

In `Rise` vocabulary:

> A function on a homogeneous `⋮`-typed type has a
> *finite-information essence*.  Essence extraction is the
> suspension move that confines the function's vertical recursion
> into a horizontal arithmetic cell.  The decision procedure is the
> consumer of the suspended essence.

This is the formal cash-out of "only the length counts": *the
length is the entirety of the suspended essence*.

### Scope and ordering

Layer 4-Lite is implementable **independently** of Layers 3 and
4-Full.  It is a self-contained decision procedure for a useful
sublanguage.  The implementation order changes to put it *before*
Layer 3:

1. Layer 1 (interpreter) — ~1 week
2. Layer 2 (narrowing) — ~1 week
3. **Layer 4-Lite (essence + Presburger)** — ~2 weeks
4. Layer 3 (user theorems) — ~1 week
5. Layer 4-Full (IH-stop) — ~2-4 weeks

The big shift: putting **Layer 4-Lite before Layer 3** means
*automatic* decidability for the practical homogeneous fragment
*before* asking the user to write any theorems.  That's the path
of "many problems automatically decided" *realised at low cost*.

## Hyper / LogicT connection

LogicT's representation:

```haskell
LogicT m a = forall r. (a -> m r -> m r) -> m r -> m r
```

is the dual-continuation shape Hyper formalises: the `a -> m r ->
m r` is the "here's a success + how-to-continue" continuation; the
trailing `m r` is failure.  Backtracking, interleaving, and cuts all
emerge from how these continuations get composed.

Concretely, a search step is `Hyper Search-State Answer`-shaped:
invoke it against its dual to advance; the dual encodes the "try the
next branch" knowledge.  This is exactly the
calling-convention-as-hyperfunction pattern from the `38d9ed6`
git-note, instantiated at "search column" instead of "function
call column."

### Stops as Rise suspensions

Each *stop-and-reason* point in the search is a **suspension** on
the search column:

- The column = the recursive narrowing tree.
- A stop takes a finite vertical footing (the explored subtree) and
  *confines* it into a single named verdict.
- The verdict is emitted as a horizontal cell; the search continues
  past the stop with the verdict in scope.

In `Rise`-vocabulary terms (PLAN.md "Hyper-rise" section):

```
search column   = Γ Search-Step Subst Subst
stop-and-reason = retreat (collapse [explored-subtree], rest)
```

Confluence-stop, theorem-stop, IH-stop are all instances of this
move at different granularities.

### What the substrate looks like

```haskell
type Narrow = LogicT (ReaderT Env (StateT Subst Identity))

meet :: TyProc -> TyProc -> Narrow ()
meet l r = do
  (l', r') <- normalise l r  -- Layer 1: demote-interp-promote
  case (headShape l', headShape r') of
    Equal -> pure ()           -- confluence-stop
    Mismatch -> mzero          -- conflict-stop (fail)
    Stuck m -> caseSplit m     -- Layer 2: narrow
    NeedsTheorem g -> rewrite g  -- Layer 3: theorem-stop
    NeedsIH g -> applyIH g    -- Layer 4: IH-stop
```

The five "stops" partition the narrowing engine's actions.  Each is
a guard that pattern-matches the current goal-shape and either
emits a verdict or transitions to another shape.

## Conjecture about decidability

The user's claim — *"many problems can be automatically decided"* —
deserves unpacking.  At Layer 4 (LogicT + IH-stop + theorem-stop),
the decidable fragment includes:

- All equalities between functions that recurse on the *same*
  structural argument (the `add`/`add'` shape).  Even non-trivial
  equalities (`add a Z = a`, etc.) close automatically by induction
  on the recursion arg.
- All equalities directly entailed by registered theorems (Layer 3
  always works for these).
- All equalities between concrete-arg expressions (Layer 1 alone).

The *not*-automatically-decidable fragment:

- Equalities between functions with *different* recursion structure
  (e.g., `add` recurses on first arg, `mul` on second).  Requires
  auxiliary lemmas that the user must register; the engine then
  applies them but doesn't discover them.
- Equalities requiring more than one level of nested induction with
  non-obvious termination metric.  Standard limits of Agda/Coq's
  automated tactics.

Practically, the "automatically decidable" fragment is enormous —
most equational reasoning in functional-language libraries falls
under it.  The Ωmega/Idris/Agda experience confirms.

## Connection to existing constructor work

What's already in place:

- **HypTwr's `meet`**: the unification entry point where narrowing
  slots in.  Currently first-order; would become LogicT-monadic.
- **`Constructor.HyperRise`**: the Rise substrate that the search
  column rides on.  Each stop is a suspension.
- **`⋮` annotation + tyBinders**: the value/type bridge.  Demote /
  promote operates over `⋮`-typed positions.
- **Pure functional value-level**: no IO, no mutation.  The
  interpreter has nothing to fight.
- **`elabCtorApp`** (existing): introduces fresh metas at use sites
  (the seeds for narrowing).
- **CtorSig extraction** (existing): tells us which ctors are
  inhabitants when narrowing a meta.

What's missing (still ahead):

- **Multi-arg / unary-ctor narrowing**: current Phase D only
  enumerates nullary ctors at meta-arg positions.  Unary ctors
  (`S _`, `Cons _ _`) need fresh sub-meta generation.
- **Disjunctive search**: current implementation takes first-wins;
  full narrowing should track all branches (disjunctive
  refinements).
- **`Hyper`-LogicT substrate**: replace the plain `[]`-list bag
  used for candidates with Kidney/Wu's hyperfunction-based monad.
  Gives proper interleaving + backtracking + cuts.
- **Theorem registry** (Layer 3): parser + AST + env + rewrite.
- **Homogeneous-type Presburger** (Layer 4-Lite): essence
  extraction + Cooper's algorithm port.
- **Termination / IH apparatus** (Layer 4-Full): structural-
  recursion check + active-goal stack + IH-matcher.

## Implementation history and ordering

**Originally planned** (path-of-least-resistance, 2026-05-31):
1 → 2 → 4-Lite → 3 → 4-Full, with each step ~1-4 weeks.

**Actually executed** (2026-06-01):

1. ✅ **Layer 1 split into A+B+C.**  Three discrete commits rather
   than one Layer-1 land:
   - **A.** Slide-down `var` → `TyDeferV` on `TyUnbound`
     (`04eef5c`).  The "lookup-then-defer" reflex that makes
     value-level bindings reachable from type position.
   - **B.** Value-level interpreter `Constructor.Interp`
     (`f89dd6f`).  Standalone module; tests via hand-built Exprs.
   - **C.** Bridge — demote/interp/promote in HypTwr's `meetNorm`
     wrapper (`df54e4a`).  Wires A's TyDeferV into B's interp.
2. ✅ **Layer 2 minimal** (`5194a31`).  Narrowing on stuck meta
   args; nullary ctors only.  Uses plain `[]`-list bag for
   candidates (Hyper-LogicT deferred).

**Still ahead**, in expected order:

3. **Layer 2 expansion** — unary-ctor narrowing (fresh sub-meta
   generation), disjunctive all-branches search.  ~1 week.
4. **Hyper-LogicT substrate** — replace `[]` bag with Kidney/Wu's
   construction.  ~1-2 weeks.
5. **Add Layer 4-Lite** — homogeneity detection + essence
   extraction + Cooper's algorithm.  ~2 weeks.  Decides the
   one-dimensional homogeneous fragment (commutativity,
   associativity, identity laws, monus, min/max — anything in
   Presburger arithmetic).  Self-contained.
6. **Add theorem signature** (Layer 3).  Parser, AST node, env
   entry, rewrite step in narrowing.  Trusted axioms only at
   first.  ~1 week.  Covers the nonlinear / multi-type fragment
   that 4-Lite doesn't reach.
7. **Add IH-stop** (Layer 4-Full).  Termination order,
   active-goal tracking, IH-matcher.  ~2-4 weeks.  Real
   automation for the branching / mixed-type cases.

What landed (1+2-min) is the practical first milestone: automatic
demote-interp-promote for concrete-arg cases, with case-split
narrowing on nullary metas as fallback.  This covers the original
"is `Refl on Eq Z (pickZ Z)` typeable?" question — yes, with the
right declarations.  The remaining Layers/upgrades enrich the
decidable fragment toward Ωmega and Agda-style automation.

## The Rise pay-off, restated

Every aspect of narrowing fits the existing Rise / (γ) algebra:

- Search column = `(γ) Search-Step Subst Subst`.
- Case-split = horizontal step (lateral expansion in `meet`).
- Recursion = vertical step (kindOf-equivalent on the search
  column).
- Stop-and-reason = suspension of a finite search subtree into a
  named verdict.
- IH-stop = the suspension is justified by the rise's structural
  recursion order (termination metric).
- Theorem-stop = the suspension is justified by a registered
  equational rewrite.
- Erasure at the bottom = once narrowing finishes, only the resulting
  `Subst` survives; the entire search column is gone (compile-time
  artifact).

The same framework that powers the Wasm codegen vision powers the
narrowing engine.  Different lateral content (`Search-Step` vs
`WasmFrag`), same column-and-suspension algebra.

## References

- `Constructor.HyperRise` — substrate for the search column.
- `~/hyperfunctions/constructor/PLAN.md` — "Hyper-rise" section.
- Git-note on `38d9ed6` — calling-convention-as-(γ) framing.
- LogicT — Kiselyov, Shan, Friedman, Sabry, "Backtracking,
  Interleaving, and Terminating Monad Transformers"
  (ICFP 2005).  The classical reference.
- Ωmega — the language that established the
  narrowing-with-theorems pattern in a Haskell-flavoured setting.
- Agda's tactic system + termination checker — the bar for
  Layer 4 automation.

## TL;DR

Five layers, each a strict extension; Layer 4-Lite lives between
Layer 2 and Layer 3 in the implementation order because it gets
automatic decidability on the practical homogeneous fragment without
user input:

| Layer | Mechanism | Status | Unlocks |
|---|---|---|---|
| 1 | Demote-interpret-promote across `⋮`-iso | ✅ landed | Closed-term type-level evaluation |
| 2 | Narrowing (case-split on stuck metas) | ✅ minimal landed | Decidable case-split trees (nullary ctors so far) |
| 4-Lite | Essence extraction + Presburger decision | ⏳ pending | One-dimensional homogeneous types; +, -, min/max identities — automatically |
| 3 | Equational theorems as rewrites | ⏳ pending | User-supplied lemmas; nonlinear / multi-type fragment |
| 4-Full | Automatic IH reuse via structural recursion | ⏳ pending | Agda-style; branching types |
| Hyper-LogicT substrate | Replace `[]`-bag with Kidney/Wu's monad | ⏳ pending | Proper interleaving + cuts |

Each layer maps to suspension primitives on a Hyper/LogicT-based
search column.  The homogeneous fragment (Layer 4-Lite) covers
commutativity, associativity, identity laws, monus, min/max —
essentially Presburger arithmetic on lengths.

**Done so far** (2026-06-01): Layers 1 + 2-minimal.  The bridge
demote-interp-promote works end-to-end; case-split narrowing fires
on nullary metas; the test `data Wit (n : Nat) { W : pickZ n ->
Wit n }; let rt = W Z` typechecks with `?n := Z` refinement.

**Path ahead**: expand Layer 2 (unary ctors, disjunctive), then
Hyper-LogicT, then Layer 4-Lite, then Layer 3, then Layer 4-Full.
