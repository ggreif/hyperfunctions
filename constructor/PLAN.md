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

## Type-inference arc — commits 2, 3 (landed) and 4+ (planned)

The level-inference layer is closed at v_polymorphic.  The type-
inference arc now opens.  The corpus's parser is annotation-agnostic
already; both arms can be added under `Lang` instances without parser
changes.

### Commit 2 (landed) — `TyExpr` + `Tinf` (A side, baseline)

Value-level types live in `Constructor.TyExpr`:

```haskell
data TyExpr
  = TyVar  !Name !Path           -- variable, identified by its binder path
  | TyCon  !Name                 -- nullary type constructor reference
  | TyApp  !TyExpr !TyExpr       -- type-level application: f x
  | TyArr  !TyExpr !TyExpr       -- function type: a -> b
  | TyUniv !Lv                   -- universe at a given level
```

`Constructor.Tinf` is the A-side carrier: a small state-threading
elaborator that produces a `TyResult` (declared data types + their
arities, declared constructors with elaborated types).  No Robinson
unification yet — each `TyExpr` is fully concrete at construction.
This is the *control* arm against which B is to be benchmarked, the
way `Tc` is the control arm for the level-inference experiments.

### Commit 3 (landed) — use-site path-combining (Stern-Gerlach)

Type-parameter occurrences inside a `data Foo a { … }` body now carry
the **binder's** path, not just the surface name `"a"`.  The parser
threads a `Binders` record with two namespaces (`lvBinders` for `∀l.`
binders, `tyBinders` for `data` parameters), allocates parameter paths
as `extendPath (PsDataParam i)` off the data declaration's own path,
and emits a new `Lang` method:

```haskell
tyParamRef :: a 'SExpr -> Name -> Path -> r a 'SExpr
```

So two distinct `data X a { … }` declarations in the same program
produce two *distinct* paths for their respective `a` parameters.
Inside the elaborator, both become `TyVar "a" pathⱼ` with different
`pathⱼ`s — visually the same name, structurally different.

This is the **Stern-Gerlach split**: a single surface name acquires
fine-structure under measurement, where measurement = the parser
descending into the binder.  It is the prerequisite for multi-site
polymorphic instantiation (when commit 5+ allocates a *fresh* α
per use site, the (def-path, use-path) pair becomes its identity);
without it, both A and B would conflate use-sites and have to fight
the conflation later.

`Tinf` consumes the resolved paths directly — its `var` is now
reserved for nullary type-constructor references; its new
`tyParamRef` method emits `TyVar n path` unchanged.  The
`tinfParamScope` field of `TinfEnv`, which would have done the
name-based parameter resolution, is gone — the parser owns that
work now.

### Commit 4 (next) — B-side `HypTinf` carrier

Direct sibling of `HypLinf` for type inference.  The substrate is no
longer a Sheet (or a state-threaded `TyResult`-builder) but a *web of
type-processes*, each a hyperfunction valued in a one-layer-unfolded
view of the type:

```haskell
data TyView
  = TyConV  !Name
  | TyVarV  !Name !Path
  | TyAppV  !TyProc !TyProc
  | TyArrV  !TyProc !TyProc
  | TyUnivV !Lv
  | TyMetaV !Path !Path    -- fresh metavariable at (def-path, use-path)
                           -- — dormant in commit 4, activated later

type TyProc = Hyper TyView TyView
```

The HKT'd carrier mirrors `HypLinf`:

```haskell
data HypTinfVal (s :: Sort) where
  HypTinfExpr :: !TyProc                         -> HypTinfVal 'SExpr
  HypTinfDecl :: !(Maybe (Name, TyProc))         -> HypTinfVal 'SDecl
  HypTinfProg ::                                    HypTinfVal 'SProg
```

A type-process is **what its peer-callback exposes when interrogated**.
Constructing it from a `TyExpr` is the identity coalgebra: `tyToProc t
= hPure (oneLayer t)` where `oneLayer` is the one-step unfolding into
`TyView` (children remain as `TyProc`s by recursion).  Running it
back out is the dual unfold (the "probe" / final-coalgebra unfolding
that the memory file's design discussion converged on as the right
extraction story — *no* shadow state, no Tree on the side; the
unfolder is itself a hyperfunction-style traversal).

Commit 4's scope (the **carrier+apparatus** middle ground):

- New module `Constructor.TyProc` — `TyView`, `TyProc`, `tyToProc`,
  `procToTy` (the probe-unfolder), and `meet :: TyProc -> TyProc ->
  Either TyErr TyProc` over structurally-concrete views only.  The
  `TyMetaV` constructor is in place so the carrier *shape* is right,
  but unification of metavariables is deferred to commit 5.
- New module `Constructor.HypTinf` — the `Lang HypTinf` instance,
  mirroring `Tinf`'s structure.  `tyParamRef` builds a `TyMetaV`-free
  `TyVarV` process (commit 4 shares one process across all uses of
  the same binder; commit 5 promotes to per-use fresh α).
- Parity tests: `HypTinf` vs `Tinf` on the existing corpus must agree
  modulo extraction.  Plus the Stern-Gerlach test in process form.

### Commit 5 (landed) — `meet` apparatus, concrete-only

Pure structural unification on type-processes for the concrete-
concrete fragment.  Matching heads (`TyConV`, `TyVarV`, `TyAppV`,
`TyArrV`, `TyUnivV`) recurse into their children; mismatched heads
return `TyMismatch`.  Direct unit tests in `TyProcSpec` exercise the
algebra without a carrier path.

The `TyMetaV` parking slot reserved in commit 4 stays unbuilt in
commit 5; the customer for metavariable unification doesn't arrive
until commit 6, when parametric tycon applications start allocating
fresh metas.

### Commit 5.5 (landed) — def-path identity for `TyCon`

The Stern-Gerlach binder discipline now applies uniformly to type
constructors (alongside type parameters and `∀l.`-binders).  For
nullary tycons the use-path collapses to the def-path \(x^0 = 1\);
for higher-kinded uses (commit 6) the use-path becomes load-bearing
as the address for fresh α-cells.

### Commit 6 (landed) — metavariables, redirect-encoded `meet`,
### parametric instantiation customer

The genuine algebraic workout.  Three load-bearing pieces:

1. **Metavariables as identified cells.**  `TyView` activates its
   `TyMetaV` constructor, now carrying a `MetaId = MetaId !Path
   !Path` (binder-path × use-path).  The first 'Path' is the
   parameter binder's def-position (`extendPath (PsDataParam i)
   declPath`); the second is the application-as-a-whole's syntactic
   path, supplied to `Lang.app` by the parser.  Two distinct
   `List Nat` and `List Bool` use-sites produce metas with distinct
   identities; same-position uses share identity.

2. **Redirect-encoded substitution.**  `meet` is now Subst-threaded:

   ```haskell
   meet :: Subst -> TyProc -> TyProc -> Either TyErr Subst
   ```

   When `meet α concrete` resolves a meta, the binding lands in the
   `Subst` as `α ↦ concreteView` — and that view may itself mention
   other metas.  `meet` does **not** eagerly chase chains; subsequent
   `materialize` (or further `meet` calls) traverse through.  The
   encoding is the *redirect* one from the design conversation —
   git's merge-commit, not squash; one indirection per rewire,
   history walkable.  The `π₁`-flavoured trace the memory file
   describes is now an observable property: two unifications of the
   same pair α ≡ β via different routes leave distinct chains.

   `Subst = Map MetaId TyView`; `emptySubst = Map.empty`.  No occurs
   check yet — cyclic metas would loop `materialize`.  A later
   commit adds the standard guard.

3. **Parametric instantiation in `HypTinf.app`.**  The first carrier
   customer for `meet`.  When elaborating a type-level application
   whose head is a parametric tycon, the carrier:

   - walks the function-position spine of the application,
     counting how many arguments have already been consumed
     (depth);
   - looks up the tycon's arity;
   - allocates a fresh meta at `(extendPath (PsDataParam depth)
     declPath, appPath)` — Stern-Gerlach addressing across both the
     parameter binder and the use site;
   - calls `meet` against the supplied argument's process,
     extending the carrier's `Subst`.

   Arity violations surface as `TyArityMismatch`.  Non-tycon heads
   (e.g. an unresolved free variable) flow through untouched.

   `HypTinfResult` now exposes the accumulated `Subst`;
   `hypTinfCtorTypes :: HypTinfResult -> Either TyErr (Map Name
   TyExpr)` calls `materialize` per ctor.  Parity with `Tinf` holds
   because under-`materialize` extraction produces the same
   syntactic types — the algebraic difference is in *what's
   recorded* (B carries the substitution; A doesn't).

The `Lang.app` signature gained a `Path` argument to carry the
application's path-as-a-whole.  Every nested `App` within one
source-level application shares this path — different applications
at different syntactic positions get different paths, supplying the
fresh-α addressing that multi-site distinction depends on.

### Commits 7+ — the Tower arc

The natural continuation isn't an occurs check or a decoration
retrofit; it's a substantive shift in *what the carrier value
represents*.  The current `TyProc` describes a node's type at one
rung above it.  The Tower is the same idea taken **coinductively all
the way up**: each carrier value exposes not just the type of its
source node but its entire upward typing tower — type, kind,
super-kind, and so on, as codata.

#### The deck-group reading

Three kinds of cell in the cover, with sharply different algebraic
properties:

| generator | what it moves | algebraic shape |
|---|---|---|
| `S` (level successor on `Lv`)             | the level-coordinate | partial bijection — `S^{-1}` works at every interior point, fails only at zero |
| horizontal `data`-decl directions (`List`, `Maybe`, `Pair`, …) | within a rung | groupoid morphisms — invertible via fresh-metavariable allocation; the existing `meet` / Subst machinery is exactly the path-tracing in this groupoid |
| `:` (the typing colon)                    | between rungs        | directed morphism — `:^{-1}` is *totally* lossy (the fibre over any type is the set of all its inhabitants); no canonical retract anywhere |

`S` and `:` agree only along the universe-ladder spine
`*0 : *1 : *2 : …` where the cover entries happen to be the level
counters themselves; off-spine, `S = level ∘ (:)` is just the
projection of `:` onto the level coordinate.  The genuinely directed
cell is `:`; `S` is its image under a projection that forgets
everything except how many rungs were crossed.

The horizontals plus `S^{-1}` live in the **groupoid** part of the
covering space (∞-groupoid / plain π₁).  `:` lives in the
**directed** part (∞-category / directed π₁ — Riehl–Shulman's
ambient).  The two glue together to form a directed ∞-category;
that is the operational realisation of the directed-HoTT thread the
memory file talks about.

#### Compressibility, not concentration

Earlier framing claimed information "concentrates at low rungs."
That's wrong as stated — universe-polymorphic `data` can populate
every rung as densely as you like.  The correct invariant is
**stabilisation modulo parametricity**: after a finite application
of `:` the Tower's shape becomes representable in finite data —
either a plain successor stream (monomorphic terms) or a finite
parametric form in some level variable (`∀l.`-polymorphic terms).
Codata with a finite generator.  This is what makes the tower
representable at all; it's not "the upper rungs are trivial" but
"the productive program generating them is finite."

#### Coalgebraic tail-then-head as the unifying story

Standard type inference is **catamorphic**: build up from leaves
toward root via fold.  Tower inference is **anamorphic** on the
vertical axis: fix the tail (the stable, finite-generator
representable part), then unfold downward to constrain the head
(the actual term we want to check).

In this dialect:

- **Kind inference** = unfold one rung downward.  "What's the type
  of this type" is the unfold step that produces the next-lower
  view given the rung above.
- **Super-kind inference** = the same unfold step indexed one rung
  higher.
- **Universe polymorphism** = a parametrically-finite tail whose
  rungs are functions of a free level variable.
- **Type checking** at any rung = catamorphic recursion at that
  rung's horizontal structure, anamorphic step to the rung above.

The whole upward stack is one coalgebra; current `Tinf` /
`HypTinf` are the bottom-rung specialisation.

Why hyperfunctions are the right substrate for this: hyperfunctions
are *both* fold and unfold-capable — `Category`/`ana`/`cata`
instances on `Hyper a b` give us the bidirectional algebra out of
the box.  A's `TyExpr` is a finite tree; it cannot represent the
tail of a tower in parametric-finite-generator form without bolting
on a separate side-channel (which is exactly what today's level
layer *is* — A's bolt-on for the vertical axis).  B's Tower carries
the productive generator inline.  This is where the hyperfunction
encoding earns its keep over a stateful Robinson-with-substitution.

#### Tower encoding (option β)

The pragmatic middle ground between thin (`Hyper TyView TyView`
with implicit advance via repeated `hRun`) and fully self-typed
(`Tower ≅ Hyper Tower Tower`, Lambek-style):

```haskell
-- sketch
data Tower = Tower
  { horizontal :: !TyView   -- groupoid-flavoured layer:
                            -- parametric structure, subject to `meet`
                            -- and metavariable allocation
  , vertical   :: !Tower    -- directed `:` step upward, lazily
                            -- (codata); never inverted, never
                            -- subject to symmetric unification
  }
```

The two slots have **different equational theories**: horizontal
unification is groupoid-coherent (UIP-ish, metavariable-invertible);
vertical unification is directed (subtyping/coercion-flavoured, no
canonical inversion).  Conflating them would lose information that
the design depends on.

#### The four-commit Tower arc

1. **`Tower` lift + parity scaffold (landed).**  Introduced `Tower`
   per (β).  Lifted the existing level-layer's `Lv`-per-node info
   into vertical rungs of a per-term Tower; lifted `TyProc` into the
   horizontal slot.  New module `Constructor.Tower`; no carrier
   changes.  Parity tests verify "extract first-rung-view from a
   Tower matches today's `procToTy` output."

2. **Coalgebraic `infer` step (landed).**  One unfold of the
   Tower's vertical given the horizontal — `kindOf : KindEnv ->
   TyView -> TyView`, the elementary kind-inference move.
   Re-applied, it's super-kind inference.  `HypTinf` now collects
   `hypEnvKindEnv` while elaborating each `data X : K`'s annotation,
   so `kindOf` consults declared kinds rather than the synthetic
   universe stream of commit 7.  This is the commit where "kind
   inference" became a real notion in the codebase: not as a
   separate pass, but as a coalgebraic step re-indexable by rung.

3. **Tower-aware kind coherence + meet (landed).**  Walks two Towers
   rung-by-rung along the vertical axis; termination is guaranteed by
   the `*n`-stable-tail (the `x^0 = 1` collapse from the
   covering-space framing).  Two entry points: `compareTowers` (pure
   yes/no parity) and `meetTowers :: Subst -> Tower -> Tower -> Either
   TyErr Subst` (groupoid-flavoured horizontal meet via the existing
   `TyProc.meet`, threaded through the Subst at each rung;
   directed-flavoured vertical walk).  `HypTinf.dataDecl` threads a
   `Maybe (Name, Path)` parent context and, on a nested `data Y :
   K_Y` inside `data X : K`, builds Y's annotation tower against the
   parent's TyConV-tower; mismatch (e.g. `data Ty2 : *0` inside `data
   Type : *1`) is rejected with `TyMismatch` at elaboration time.
   `Constructor.HyperLite` gained Ed Kmett's `Category` instance for
   the future composition machinery.  Limitation: a metavariable
   resolution at rung *n* does not yet re-generate the towers'
   verticals for rung *n+1* onward — the kind-check path threads no
   metas today, but a tower-aware occurs check will need to close
   that loop.

4. **`HypTwr` carrier (landed).**  New `Lang` instance whose `SExpr`
   carrier value is a 'Tower' directly (rather than a 'TyProc' with
   tower computed on demand).  Parallel sibling of `HypTinf`; the
   `HypLinf → HypTwr` pipeline replicates the `HypLinf → HypTinf`
   shape.  Each method emits a fully-formed up-tower whose vertical
   is generated coinductively by 'kindOf' from the env's kind
   annotations.  `HypTwrSpec` carries parity tests against `HypTinf`
   on the metavariable-free corpus — both extract the same ctor
   types and data-arity maps.  For commit-4 scope the
   parametric-meta customer that 'HypTinf.app' runs (allocate a
   meta per parametric tycon position, unify with the supplied
   argument, record in 'Subst') is intentionally omitted; the
   horizontal shape extracts identically on the corpus and the meta
   layer can be retrofitted alongside the future tower-aware
   occurs check.

#### Beyond the four-commit arc

The arc proper is now complete.  Two follow-ups sit at the seam:

- **Stratified self-typing — `data Weird : Weird` (Tower layer
  landed; level-layer end-to-end pending).**  'TyConV' grew a deck-
  shift offset `!Lv`; 'kindOf' on a TyConV whose env-bound kind
  annotation is itself (modulo Name + Path) bumps the offset by one
  instead of recursing, giving productive codata up the rungs.
  'meetTowers'/'compareTowers' gained a TyConV-stable-tail base
  case (same Name, Path, and offset → success).  Tower-layer
  tests in 'TowerSpec' build a Weird-tower under a synthetic
  KindEnv and verify both productive climbing and immediate
  termination on identical towers.  End-to-end through HypLinf is
  still blocked: HypLinf rejects 'data Weird : Weird' at level
  elaboration because the name isn't in scope while its own kind
  annotation is being elaborated, and `predLv (LVar _) = Nothing`
  has no fixpoint for `n = predLv n`.  Two related accommodations
  unblock end-to-end:
    - HypLinf.dataDecl pre-binds `n` (to a tentative LVar declPath)
      before elaborating the kind annotation, so the self-reference
      can resolve.
    - `predLv (LVar p)` returns `Just (LVar p)` (the LVar is its
      own predecessor — the level coordinate is fully parametric),
      letting `data Weird : Weird` settle at a level-polymorphic
      level rather than failing 'DataAnnotationTooLow'.
  The deck-shift slot already sitting on 'Place' in 'Sheet.hs' is
  the A-side analog of the TyConV offset — present since v0
  anticipating exactly this move.

- **Tower-aware occurs check (landed).**  Two layers:
    - **Structural occurs in 'TyProc.meet'.**  Before binding @m
      := v@, 'meet' calls 'occurs s m v' which walks @v@'s
      structure (chasing 'Subst' through 'resolveView' and
      recursing into 'TyAppV' / 'TyArrV' children).  Returns
      'TyOccursCheck bp up' on a hit.  Catches the classical
      Robinson cases (@m := List m@, @m := Nat -> m@, transitive
      cycles via prior bindings).
    - **Tower-occurs guard in 'meetTowers'.**  Before each meet
      step's delegate to 'TyProc.meet', if one side resolves to
      a 'TyMetaV' @m@ and the other side's upward tower
      (regenerated via 'kindOf s env' until a stable tail or a
      hit) mentions @m@ at any rung, the binding is refused with
      'TyTowerOccurs bp up'.  Catches the cases structural
      misses — @m@ horizontally absent at rung 0 but reachable
      through the type's kind chain (e.g. @data X : m@ where
      the kind annotation IS @m@; binding @m := X@ would close a
      cycle through the typing tower).  The 'TyConV'-tail base
      case ('offset > 0') stops the walk on legitimate
      Weird-style self-stratification — the productive
      offset-bumping stream can't re-introduce a fresh meta.
    Five tests document both: three structural (List m, Nat -> m,
    transitive) and two tower-aware (meta-induced cycle through
    env caught; legitimate Weird-style not caught).  The
    tower-aware test is verified load-bearing by temporarily
    disabling the guard — the test then fails as predicted,
    confirming the guard isn't redundant with structural occurs.

- **Meta-aware vertical regeneration (landed).**  `kindOf` is now
  a natural family indexed by `Subst`: `kindOf :: Subst -> KindEnv
  -> TyView -> TyView`, internally calling 'resolveView s' before
  processing.  The categorical content: the square
  ```
            kindOf s
        v ─────────► kindOf s v
        │              │
   resolve s'      resolve s'
        ▼              ▼
   resolve s' v ─► kindOf s' (resolve s' v)
            kindOf s'
  ```
  commutes against substitution extension `s ⊑ s'`.  Without the
  resolveView at entry the square doesn't close — climb-then-
  resolve and resolve-then-climb land at different views, and
  every subsequent climb compounds the divergence.
  'meetTowers' was updated to regenerate the climb via 'kindOf'
  under the just-extended Subst rather than walking the towers'
  frozen 'vertical' chains; the static codata is fine for
  meta-blind 'compareTowers' but a tower constructed under one
  Subst can't speak for an extended one without re-evaluation.
  Two 'TowerSpec' tests witness: a meta-vs-concrete meet now
  walks all the way to the '*n'-stable tail (binding the meta
  *and* propagating the binding upward), and the naturality
  property is verified in concrete numbers against an
  out-of-band Subst.  Removing the 'resolveView' at 'kindOf'
  entry causes the first test to fail with structural
  TyMismatch, demonstrating the load-bearing nature of the
  naturality fix.

The end-of-arc decoration question dissolves: B's Tower is the
decoration — each `SExpr` carrier value *is* the decorated
form, recursively all the way up.  A would need a parallel
non-codata structure to keep up; we'd defer that until a downstream
consumer actually demands the A-side analog.

#### Non-spine cycles: deferred

`data Weird : Weird` looks self-referential but is, in our system,
just universe-polymorphism shorthand: `data Weird : ∀l. *l { … }`,
with the annotation `: Weird` standing for `: Weird{l+1}`.  Each
instance climbs the ladder.  Our existing `∀l.` machinery handles
this already.

The *genuinely* non-stratified case — monomorphic `Weird : Weird`
forming a `:`-cycle (the Type : Type / Girard's paradox territory) —
is **not** in scope for the Tower arc.  It would require switching
`Lv` from inductive `ℕ`-shaped to coinductive (productive but
possibly cyclic) and accepting the loss of consistency-as-a-logic
in exchange for cyclic self-typing as a programming construct.
That's a separate design knob, orthogonal to the Tower work.

#### Connection to opetopes / globes

Finster's coinductive globular composition (and opetopic
generalisations) is the *dual* growth direction to ours: their
tower goes dimension-up (k-cells → (k+1)-cells); ours goes
typing-up (rung-n → rung-(n+1)).  Both are coalgebraic on the same
`Hyper`-style algebra; both have "infinite tower with finite
productive generator" as the canonical representation.  If we ever
combined the two — directed ∞-categorical types where each rung of
the typing tower has its own higher-cell structure — opetopes
supply the cell shapes, hyperfunctions supply the unfolding
mechanism, and our `:`-vs-horizontal axis split tells you which
cells are directed and which are groupoid.

That's the full directed-HoTT operational picture; the Tower arc
above is its tractable first step.

### Why these commits, in this order

The path-combining-before-B-side reorder happened because both A and
B would otherwise need to be retrofitted with Stern-Gerlach
simultaneously.  Doing path-combining once, in shared infrastructure,
lets both carriers consume the resolved paths from the parser
identically.  B then enters with the right vocabulary already.

The carrier+apparatus middle ground for commit 4 buys the natural
seam without overcommitting: the `TyView` shape (including its
`TyMetaV` slot) is the data structure both for commit 4's
extension-free elaboration and for commit 5's unification.  Adding
unification logic later doesn't reshape the algebra.
