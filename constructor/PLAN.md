# Constructor language — design notes

## Carrier shape: HKT-parameterised by annotation

The finally-tagless `Lang` class is HKT'd:

```haskell
class Lang (r :: (Sort -> Type) -> Sort -> Type) where
  star :: a 'SExpr -> Word -> r a 'SExpr
  arr  :: a 'SExpr -> r a 'SExpr -> r a 'SExpr -> r a 'SExpr
  ...
```

Where `a :: Sort -> Type` is the annotation kind (Trees-that-Grow
style: each sort gets its own slot) and `r :: (Sort -> Type) -> Sort
-> Type` is the carrier — typically a tree, a monadic computation, or
both.

### Why HKT now, not later

We will run the same grammar through several phases:

| phase                 | annotation              | carrier shape                                       |
|-----------------------|-------------------------|-----------------------------------------------------|
| raw parsing           | `Const ()`              | `Tree (Const ())`                                   |
| level inference (v0)  | (phantom; uses sheet)   | `Lvl a` (a is unused; substrate threads info)       |
| type inference        | `TcAnn` (with `Place`)  | `Tree TcAnn` decorated alongside constraint emit    |

With the older `r :: Sort -> Type` shape, each phase needed its own
`Lang` instance even though the tree structure was identical — N
phases ⇒ N instances of the same plumbing.  Worse, every new
annotation regime forced touching the parser, every interpreter, and
every test type signature.

The HKT'd shape replaces those N instances with **one** polymorphic
instance per *carrier*, parameterised in the annotation:

```haskell
instance Lang Tree where
  star ann n = Star ann n
  arr  ann a b = Arr ann a b
  ...
```

Phases differ only in (a) the annotation type they instantiate `a` to
and (b) the `HasAnn` instance that produces those annotations.

### Annotation production: `HasAnn`

The parser is annotation-agnostic.  It obtains annotations through a
separate, monad-parameterised typeclass:

```haskell
class Applicative m => HasAnn (a :: Sort -> Type) (m :: Type -> Type) where
  freshExprAnn :: m (a 'SExpr)
  freshDeclAnn :: m (a 'SDecl)
  freshProgAnn :: m (a 'SProg)
```

For the raw phase, `HasAnn (Const ()) m` is trivial for any
applicative `m`.  For the type-inference phase, the parser monad will
be stacked on top of the constraint generator, and `HasAnn TcAnn m`
will allocate a fresh `Place` from the sheet each time a fresh
annotation is requested.

The grammar functions (`expr`, `decl`, `program`, …) don't change
between phases — only the parser monad and the `HasAnn` instance do.

### Cost paid up front, savings deferred

The HKT'd class adds one type parameter to every method signature and
forces explicit `freshXxxAnn` calls at every node-construction site in
the parser.  In return, *adding* a new phase becomes:

1. Declare the annotation type, `data NewAnn (s :: Sort) where …`.
2. Write a `HasAnn NewAnn m` instance for the appropriate parser monad.
3. Reuse all existing grammar.

The alternative — defer this refactor until type inference arrives —
would touch every consumer of `Lang r => …` at the time when the
codebase is larger and the migration is more invasive.  Doing it now,
while there are 4 modules and 14 tests, costs about a screen of
type-signature churn and zero behavioural change.

## Substrate: union-find on the sheet

Constraint solving (level inference today, type inference later) sits
on a union-find structure in `Constructor.Sheet`:

- `Place` carries an `Int` id and a forward-looking `placeOffset :: Lv`
  deck-shift slot (always `Z` in v0, will hold non-trivial offsets
  once universe polymorphism arrives).
- `Sheet info` is the union-find graph plus a partial map of pinned
  `info` at roots.  Parameterised in `info` so the substrate is reused
  across phases: v0 sets `info = Lv` with equality-based merge; type
  inference will set `info = TyExpr` with structural Martelli–Montanari
  merge.
- `unify` and `pin` take the merge function as a callback — the only
  thing that changes between v0 and v_types is which merge is plugged
  in.

## What v0 explicitly does *not* have

- No `data` parameters (`data List a : *0 …` waits for v_params).
- No GADT-style explicit per-constructor return types.
- No expressions other than `*n`, name, and homogeneous `→`.
- No function definitions, no pattern matching, no `case`.
- No universe polymorphism (`∀l. *(3 + l)`).  All levels are concrete.
- No level variables in the constraint solver — every `:~:` constraint
  is between two known levels.

Each of these unlocks a specific future direction; the HKT carrier
shape and the union-find substrate are exactly the seams along which
they will be added.

## Tc carrier shape — decisions from 2026-05-29

### Carrier value ≠ syntactic Tree

Building `Tree a s` IS exactly what `Lang r => r a s` evaluates to at
`r ~ Tree`.  Constructors `Prog` / `DataDecl` / … are the names the
lowercase Lang methods `prog` / `dataDecl` / … reduce to at that
carrier.  No separate "Sem" newtype is necessary — the Tree, when
*built via the lowercase vocabulary*, is already the Church-encoded
polymorphic form, just specialised at one `r`.

Consequence for `Tc`:

- The `Lang Tc` instance never patterns-matches on `Tree`.  It
  emits constraints into the substrate and tracks declared names
  in its environment.  Its value type is a small `TcVal` (Place +
  sort tag), *not* a `Tree`.
- Constructors of `Tree` appear in `Tc.hs` exactly nowhere; the
  module doesn't even import `Tree`.  Consumers that want a
  `Tree` parse separately at `r = Tree`, or specialise the
  polymorphic third slot of `Tc` at `Tree`.

### Impredicative `Tc` — analysis + polymorphic LvAnnot term

`Tc`'s `runTc` field has type

```haskell
forall r. Lang r => TcEnv -> Either LvErr (TcVal s, TcEnv, r LvAnnot s)
```

so each method does its analysis work **and** simultaneously builds
a polymorphic finally-tagless term decorated with the inferred
levels (`LvAnnot :: Sort -> Type`, carrying an `Lv` per node).

Two entry points:

- `tcProgram :: Tc a 'SProg -> Either LvErr TcResult` — analysis
  only; specialises the polymorphic slot at a trivial `Discard`
  carrier internally.
- `tcRunWith :: forall r a. Lang r => Tc a 'SProg -> Either LvErr (TcResult, r LvAnnot 'SProg)`
  — analysis **plus** the polymorphic term at the caller's chosen
  `r`.

GHC 9.10's QuickLook handles the impredicative field without
explicit type-application acrobatics; only the `@Tree` / `@Discard`
choices at the entry points need `@`.  `{-# LANGUAGE
ImpredicativeTypes #-}` is on in `Tc.hs`.

### Escape hatch if QuickLook misbehaves

Hoist `r` to be a type parameter of `Tc`, giving `Tc r a s`, and put
the `Lang r` constraint on the instance head:

```haskell
newtype Tc r a s = Tc { runTc :: TcEnv -> Either LvErr (TcVal s, TcEnv, r LvAnnot s) }
instance Lang r => Lang (Tc r) where  ...
```

No impredicativity needed; standard rank-1 Haskell.  Trade-off: the
caller picks `r` at parse time rather than at extraction time, and
re-specialisation across multiple `r` would require either re-parsing
or going through a `Tree` intermediate.  Not worse, just less
flexible.  Worth knowing in case the impredicative path ever bites.

### Solver is record projection

With name collection moved into `tcEnvNames` during the Tc pass,
`solveLevels` is just `Map.toList → resolveOne → Map.fromList` over
`TcResult`.  No `Tree` walked, no `collectNames`, no pattern matches
on syntactic structure.  The Tree-handling territory ("legitimate
non-compositional analysis") survives intact for future passes
(pretty-printer, error reporter, dependency analyser) — it just
isn't on the v0 level-inference path.

## Hyperfunctions: `HyperLite` excerpt vs the upstream package

`Constructor.HyperLite` is a deliberately minimal 17-line inline of the
`newtype Hyper a b = Hyper { invoke :: Hyper b a -> b }` formalism
(same definition as in Edward Kmett's [`hyperfunctions`](https://github.com/ekmett/hyperfunctions))
plus `hPure` and `hRun`.  We use only those two functions in v0; the
full algebra (`Category`, `Profunctor`, `Arrow`, `ArrowLoop`,
`MonadZip`, `ana`, `cata`, `push`, `project`, the `Rep`-backed
memoising variant in `Control.Monad.Hyper.Rep`) isn't needed yet.

### Why inlined, not depended-on

The upstream `hyperfunctions.cabal` pins `transformers >= 0.3 && < 0.5`,
which conflicts with GHC 9.10's bundled `transformers 0.6`.  The
upstream library doesn't actually use anything from `transformers`
that broke — `Data.Functor.Identity` and `Data.Functor.Compose` moved
to `base` years ago — so the bound is purely speculative.  Inlining
17 lines was cheaper than working around the bound for the v0 needs.

### Switch path when we want the full algebra

For Architecture B with structural type-processes (composition of
unification negotiations, profunctor-aware variance, recursive
unification via `ana`/`cata`, memoised state spaces via `Rep`), the
library starts paying off.  Migration is mechanical:

1. `~/hyperfunctions/hyperfunctions.cabal`: bump `transformers < 0.5`
   → `< 0.7` (or drop the upper bound).
2. `~/hyperfunctions/cabal.project` (new file): list both
   `./` (the package) and `./constructor/`.
3. `constructor/constructor.cabal`: add `hyperfunctions` to
   `build-depends`.
4. `Constructor.HyperLite` becomes a re-export of `Control.Monad.Hyper`
   (or is deleted and modules import directly).

No source changes required in either the library or our project.  The
bound bump is also publishable upstream as a small modernisation PR
should we choose to send it.
