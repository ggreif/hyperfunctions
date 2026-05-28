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
