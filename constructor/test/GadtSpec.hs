{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

-- | Sketches of GADT-shaped tests, with what works today vs what is
--   blocked clearly marked.  The aim of this module is to lay out
--   /typical GADT examples/ as concrete programs and confirm — via
--   the actual elaborator — exactly which corners are reachable
--   without further grammar / typing work.
--
--   What we have:
--
--     * data declarations with type-expression annotations
--     * parametric data (@data T a : *0@)
--     * forward-only sibling references (later siblings see earlier
--       ones; not vice versa)
--     * self-referential kind annotations (@data Weird : Weird@
--       Tower-style stratification)
--     * tower-aware meet + kind coherence + occurs check
--
--   What we /don't/ have yet:
--
--     * GADT result-type refinement (each ctor's result must be the
--       parent applied to its params; no per-ctor specialisation)
--     * Type-level functions
--     * Mutual-recursion between siblings (forward references into
--       not-yet-declared sibling decls)
--     * Promotion of value-level ctors to types (DataKinds-style)
--     * Value-level expressions / pattern matching
--
--   The 'reachable' section below contains genuine end-to-end tests
--   that pass through 'parser → HypLinf → HypTwr'.  The 'blocked'
--   section contains 'expect-rejection' tests that confirm what the
--   error looks like today — they'll flip to 'expect-acceptance'
--   when the corresponding feature lands.
module GadtSpec (tests) where

import Constructor.AST (Tree)
import Constructor.HypLinf (HypLinf, hypLinfRunWith)
import Constructor.HypTwr
  ( CtorSig (..)
  , HypTwr
  , HypTwrResult (..)
  , extractCtorSig
  , hypTwrCtorTypes
  , hypTwrProgram
  , hypTwrProgramWith
  , hypTwrProgramWithCtors
  )
import Constructor.Interp (extractCtorPaths, extractDataCtors, extractGlobals)
import Constructor.LevelInfer (LvErr (..))
import Constructor.Parser (parseProgram)
import Constructor.Path (Path (..), PathStep (..))
import Constructor.Syntax (Name)
import Constructor.Tinf (TyErr (..))
import Constructor.TyExpr (TyExpr (..), prettyTy)
import Constructor.TyProc (materialize)
import Data.Functor.Const (Const (..))
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Text.Megaparsec (errorBundlePretty)

tests :: [(String, IO Bool)]
tests =
  -- --- Reachable today -------------------------------------------
  --
  -- Real refining GADTs elaborate end-to-end now: kind-annotated
  -- parameters bind at the value level, the @app@ rule is
  -- loosened to accept the heterogeneous tycon-application case
  -- (Fin@1 applied to (S n)@0), the saturation check rejects
  -- structurally-wrong ctor results, and 'CtorSig' extraction
  -- packages the per-ctor refinement substitution that pattern
  -- matching consumes (see 'AxiomsSpec' for round-trip axioms).
  [ accepts "GADT sketch: Iso flat (Weird-style; all ctors : Iso)"
      "data Iso : Iso { GetOne : Iso; GetTwo : Iso; GetThree : Iso }"
      ["GetOne", "GetTwo", "GetThree"]
  , accepts "GADT sketch: Weird end-to-end (TyConRef self-reference)"
      "data Weird : Weird { Level0 : Weird }"
      ["Level0"]

  -- --- Body-mutual references (now WORKS via prescan + fallback) -
  --
  -- Parser prescan (lookAhead the body, harvest sibling names into
  -- 'tcBinders' before parsing each decl's annotation) + HypLinf
  -- parent-fallback (tyConRef lookup-miss falls back to parent's
  -- level when inside a data body) together close the body-mutual
  -- corner without DataKinds-style promotion.  The covering-space
  -- framing's "the same name inhabits multiple rungs" insight
  -- (recorded in the git-note on 78f00f4) is what makes this just
  -- bookkeeping: each ctor's value-side lives at level
  -- @predLv parent@; the same identifier as a type-side reference
  -- lives at @parent@, with the level coordinate disambiguating.
  , accepts "GADT sketch: Iso cute singleton (One : One, Two : Two, Three : Three)"
      "data Iso : Iso { One : One; Two : Two; Three : Three }"
      ["One", "Two", "Three"]
  , accepts "GADT sketch: Swap (mutual ctor-as-type — Left : Right; Right : Left)"
      "data Swap : Swap { Left : Right; Right : Left }"
      ["Left", "Right"]
    -- --- Typing-tower shorthand ⋮ ---------------------------------
    --
    -- '⋮' (U+22EE VERTICAL ELLIPSIS) is the typing-tower glyph:
    -- 'c ⋮' expands to 'c : c' (the singleton type-annotation
    -- shape).  The three vertical dots are the productive
    -- self-stratified codata above the LHS — depicting exactly
    -- what 'predLv (LVar p) = LVar p' + 'kindOf' on a TyConV
    -- compute.  Pure parser-level desugaring; no elaborator
    -- changes needed.
  , accepts "GADT sketch ⋮: Iso cute with tower shorthand"
      "data Iso \8942 { One \8942; Two \8942; Three \8942 }"
      ["One", "Two", "Three"]
  , accepts "GADT sketch ⋮: Mirror with tower shorthand on ctors only"
      -- Mixed: the data uses an explicit ∀-poly kind, ctors use ⋮.
      "data Mirror : \8704l. *l { Cup \8942; Fridge \8942; Plate \8942 }"
      ["Cup", "Fridge", "Plate"]
  , accepts "GADT sketch ⋮: Swap with tower on data, explicit ctors"
      -- Swap's ctors point at /siblings/, not themselves, so they
      -- still need the explicit annotation form.  The data line
      -- alone gets ⋮ here.
      "data Swap \8942 { Left : Right; Right : Left }"
      ["Left", "Right"]
  , accepts "GADT: Fin (n : Nat) with refining ctors — FZ : Fin Z; FS : Fin n -> Fin (S n)"
      -- The canonical refining GADT.  @FZ@'s result refines
      -- @n@ to @Z@; @FS@'s refines to @S n@ with @n@ a
      -- universally-quantified type variable at the ctor's
      -- scope (the kind-annotated parent param's @n@ — see
      -- HypLinf for the @(n : Nat)@ ↦ @predLv (level of Nat)@
      -- binding rule and the loosened @app@ that lets the
      -- type-constructor application @Fin (S n)@ type-check
      -- across levels).  Pattern matching consumes this
      -- declaration's 'CtorSig' to refine the scrutinee's
      -- index at each arm.
      "data Nat : *0 { Z : Nat; S : Nat -> Nat };\
      \data Fin (n : Nat) : *0 { FZ : Fin Z; FS : Fin n -> Fin (S n) }"
      ["FZ", "FS", "Z", "S"]
  , accepts "GADT: Expr (a : Bool) with refining ctors — Lit : Expr T; Pair : Expr T -> Expr F -> Expr F"
      -- Typed-AST shape: @Lit@'s result refines @a@ to @T@;
      -- @Pair@ takes a "true" sub-expression and a "false"
      -- sub-expression, producing a "false" one (an arbitrary
      -- type-level rule that exercises the same refinement
      -- machinery as Fin without needing arithmetic).
      "data Bool : *0 { T : Bool; F : Bool };\
      \data Expr (a : Bool) : *0 { Lit : Expr T; Pair : Expr T -> Expr F -> Expr F }"
      ["Lit", "Pair", "T", "F"]
    -- --- Existential type binder ∃ (step 3c-a) -----------------
    --
    -- '∃ m. T' introduces a fresh type variable @m@ scoped to
    -- @T@.  Step 3c-a is surface-only; refinement-on-match
    -- semantics (the gabor/gadt invariant) lands when pattern
    -- matching does.  For the body to elaborate end-to-end today,
    -- the level layer needs the body to land at the parent's
    -- level — so @∃ m. m@ alone fails (the existential's
    -- parametric level can't unify with the parent's concrete
    -- level), but @∃ m. Bool@ works (the body uses a concrete
    -- type at the right level).  Real GADT uses ('∃ m. Fin m')
    -- need arrow-kinded data + level-unification, queued for
    -- step 3c-rest.
  , accepts "GADT sketch ∃: existential m unused, body at concrete level"
      "data Bool : *0 { T : Bool; F : Bool };\
      \data Foo : *0 { c : \8707 m . Bool }"
      ["T", "F", "c"]
  , accepts "GADT sketch ∃: existential with arrow body at concrete level"
      "data Bool : *0 { T : Bool };\
      \data Foo : *0 { c : \8707 m . Bool -> Bool }"
      ["T", "c"]
  , accepts "GADT sketch ⋮: weirdo self-towering parameter (a⋮)"
      -- 'data Selfie (a⋮) ⋮ { mk : Selfie a }' — the typing-tower
      -- glyph at the param scope: 'a's kind is 'a' itself, a
      -- self-tower analogous to 'data Weird : Weird' but at the
      -- parameter level.  Parses and elaborates end-to-end
      -- because the kind annotation lives in a slot that's
      -- parsed-but-not-yet-elaborated; the closure is built
      -- (with TyConRef to a's own path) and stored, never run.
      -- When per-ctor refinement work lands, this becomes
      -- semantically load-bearing.
      "data Selfie (a\8942) \8942 { mk : Selfie a }"
      ["mk"]
  , accepts "GADT sketch ⋮: Mirror full shorthand (drops the ∀l. *l)"
      -- 'data Mirror ⋮' is Weird-style self-stratification rather
      -- than universe-polymorphic — Mirror's level is 'LVar
      -- mirrorPath' (the def's path) instead of 'LVar pBinder'
      -- (a ∀-binder's path).  Both are LVar fixpoints, so the
      -- ctor-level behaviour is observationally equivalent.
      -- More concise when you don't specifically want to
      -- introduce a ∀-binder.
      "data Mirror \8942 { Cup \8942; Fridge \8942; Plate \8942 }"
      ["Cup", "Fridge", "Plate"]

  , accepts "GADT sketch: Mirror — universe-polymorphic singleton"
      -- 'data Mirror : ∀l. *l { Cup : Cup; Fridge : Fridge; Plate : Plate }'
      -- — Iso-cute but the parent's level is parametric in @l@
      -- (an ∀-binder rather than a self-referential TyConRef).
      -- The body ctors inherit the parent's parametric level via
      -- HypLinf's parent-fallback; 'predLv (LVar p) = LVar p'
      -- doesn't care whether @p@ points at a declPath or a
      -- ∀-binderPath, so the fixpoint reasoning carries through
      -- unchanged.  Tests that the mutual-ref machinery composes
      -- with universe polymorphism.
      "data Mirror : \8704l. *l { Cup : Cup; Fridge : Fridge; Plate : Plate }"
      ["Cup", "Fridge", "Plate"]
  , rejectsAtLevel
      "GADT sketch: Mirror with typo (typo correctly caught, Unbound)"
      -- Same Mirror but with @Fridge : Frigde@ — a typo on the
      -- type side.  The parser prescan only registers actual
      -- sibling names, so 'Frigde' doesn't end up in 'tcBinders'
      -- and the parser emits @var "Frigde"@ rather than a
      -- 'tyConRef'.  HypLinf.var has no parent-fallback (only
      -- 'tyConRef' does, by design — 'var' is reserved for genuine
      -- unbound names), so the program is correctly rejected.
      -- Witnesses that the body-mutual machinery doesn't
      -- accidentally accept arbitrary forward references.
      "data Mirror : \8704l. *l { Cup : Cup; Fridge : Frigde; Plate : Plate }"
      (Unbound "Frigde")

  -- --- Top-level mutual references (now WORKS via program-level
  -- prescan + HypLinf top-level forward-ref fallback) --------------
  --
  -- The parser's 'prescanProgramDeclNames' harvests all top-level
  -- data names into 'tcBinders' before any decl is elaborated, so
  -- forward refs become 'tyConRef' rather than 'var'.  HypLinf's
  -- 'tyConRef' picks up a third fallback layer: when env-lookup
  -- AND parent-fallback both miss (i.e., at the top level
  -- referencing a not-yet-elaborated sibling data), assume the
  -- target is a self-stratified data and return @LVar path@ —
  -- exactly the fixpoint @predLv (LVar p) = LVar p@ settles the
  -- target to during its own elaboration.  Sound for the singleton
  -- family case (every member self-towers); unsound for mixed
  -- concrete-leveled forward refs (which the user can sidestep by
  -- reordering, since those don't actually need mutual).
    -- --- Per-ctor signature extraction (CtorSig) -------------------
    --
    -- 'extractCtorSig' peels each ctor's tower into argument
    -- types and result-spine refinements.  The refinements are
    -- what pattern matching will consume: matching @c@ produced
    -- by @c a b ...@ against a scrutinee of type @D s1 ... sm@
    -- unifies each @si@ with the corresponding @ri@ in the sig.
  , inspectCtorSigs
      "CtorSig: Fin refinements (FZ ↦ [Z]; FS ↦ [S n])"
      "data Nat : *0 { Z : Nat; S : Nat -> Nat };\
      \data Fin (n : Nat) : *0 { FZ : Fin Z; FS : Fin n -> Fin (S n) }"
      [ ("FZ", ["Z"])
      , ("FS", ["S n"])
      ]
  , inspectCtorSigs
      "CtorSig: Expr refinements (Lit ↦ [T]; Pair ↦ [F])"
      "data Bool : *0 { T : Bool; F : Bool };\
      \data Expr (a : Bool) : *0 { Lit : Expr T; Pair : Expr T -> Expr F -> Expr F }"
      [ ("Lit",  ["T"])
      , ("Pair", ["F"])
      ]
  , inspectCtorSigs
      "CtorSig: singleton family has empty refinements (Swap: arity 0)"
      "data Swap : Swap { Left : Right; Right : Left }"
      [ ("Left",  [])
      , ("Right", [])
      ]
    -- --- Saturation checks (HypTwr.ctorDecl) -----------------------
    --
    -- Each ctor's annotation must peel — via arrows then app spine
    -- — to a result headed by the parent tycon with the right
    -- arity.  Three failure shapes; singleton-family parents
    -- (arity 0) are exempt from the head check.
  , rejectsAtType
      "Saturation: bad result (ctor result is a parameter, not a tycon)"
      -- Lifted to the kind level so the level layer doesn't reject
      -- first: Foo's annotation @*1@ gives Foo level 2, the @(a :
      -- *1)@ binds @a@ at level 2 (= Foo's level), and @c : a@
      -- then has @lt = 2 = lp@.  Level layer passes; saturation
      -- rejects because the result is a 'TyVarV', not a 'TyConV'.
      "data Foo (a : *1) : *1 { c : a }"
      (TyCtorBadResult "c")
  , rejectsAtType
      "Saturation: wrong head (ctor of Foo (arity 1) returns Nat)"
      -- @d : Foo Z -> Nat@ — result is @Nat@, a different tycon.
      -- With parent arity 1, the singleton-family relaxation
      -- doesn't apply; rejected with 'TyCtorWrongHead'.
      "data Nat : *0 { Z : Nat; S : Nat -> Nat };\
      \data Foo (a : Nat) : *0 { c : Foo Z; d : Foo Z -> Nat }"
      (TyCtorWrongHead "d" "Foo" "Nat")
  , rejectsAtType
      "Saturation: wrong arity (Foo of arity 1 supplied 0)"
      -- @d : Foo@ — result is the parent name but applied to zero
      -- args, mismatching the declared arity of 1.
      "data Nat : *0 { Z : Nat; S : Nat -> Nat };\
      \data Foo (a : Nat) : *0 { c : Foo Z; d : Foo }"
      (TyCtorWrongArity "d" "Foo" 1 0)

    -- --- Value-level let + case (HypTwr direct elaboration) ------
    --
    -- Parsing goes straight to 'HypTwr' (skipping 'HypLinf' — the
    -- level layer has nothing meaningful to say about value-level
    -- terms; the future is on the HypTwr rails).  At this commit
    -- HypTwr only checks /scope/: every name resolves to either
    -- a let binder, a pattern-introduced binder, or a known
    -- value-level ctor.  Type-checking against 'CtorSig' lands
    -- next.
  , acceptsValByHypTwr
      "Value-level: case-of-Bool elaborates (scope-only)"
      "data Bool : *0 { T : Bool; F : Bool };\
      \let example = case T { T -> F; F -> T }"
      ["example"]
  , acceptsValByHypTwr
      "Value-level: pattern binder 'n' resolves in arm body"
      "data Nat : *0 { Z : Nat; S : Nat -> Nat };\
      \let prev = case S Z { Z -> Z; S n -> n }"
      ["prev"]
  , rejectsValAtType
      "Value-level: unbound name in let body is rejected"
      -- 'oops' is never bound — HypTwr fails with TyUnbound.
      "data Bool : *0 { T : Bool; F : Bool };\
      \let bad = oops"
      (TyUnbound "oops")
  , rejectsValAtType
      "Value-level: pattern binder doesn't leak past the arm"
      -- The binder 'n' is introduced in the second arm's pattern;
      -- the let body that references it /outside/ the case is at
      -- a scope where 'n' is no longer bound.
      "data Nat : *0 { Z : Nat; S : Nat -> Nat };\
      \let prev = case S Z { Z -> Z; S n -> Z };\
      \let leak = n"
      (TyUnbound "n")
  , rejectsValAtType
      "Value-level: heterogeneous arm bodies are rejected (Bool vs Nat)"
      -- Build-side typing now meets all arm bodies pairwise: an
      -- arm yielding @Bool@ and another yielding @Nat@ no longer
      -- meet, surfaced as 'TyMismatch'.
      "data Bool : *0 { T : Bool; F : Bool };\
      \data Nat : *0 { Z : Nat };\
      \let bad = case T { T -> T; F -> Z }"
      (TyMismatch
        (TyCon "Bool" (Path [PsProgDecl 0]))
        (TyCon "Nat"  (Path [PsProgDecl 1])))
  , rejectsValAtType
      "Value-level: parametric ctor arg-type mismatch (S applied to a Bool)"
      -- Build-side ctor typing instantiates parent param TyVarVs
      -- to fresh metas and meets each arg against the
      -- substituted 'ctorInput'.  Here @S@ wants a @Nat@ but
      -- receives a @T : Bool@ — the meet on the arg fails,
      -- caught BEFORE the case body unification step.
      "data Bool : *0 { T : Bool };\
      \data Nat : *0 { Z : Nat; S : Nat -> Nat };\
      \let bad = S T"
      (TyMismatch
        (TyCon "Nat"  (Path [PsProgDecl 1]))
        (TyCon "Bool" (Path [PsProgDecl 0])))
  , acceptsValByHypTwr
      "Value-level: GADT refinement narrows pattern binder type"
      -- The FZ arm yields a @Nat@ (@Z@) which would mismatch
      -- the FS arm's @Fin α@ body; but for scrutinee
      -- @Fin (S Z)@ the FZ pattern's @Fin Z@ refinement clashes
      -- — the arm is unreachable, its body's type doesn't
      -- enter the case's per-arm unification.  The FS m arm
      -- alone determines the result type: pattern @Fin (S α)@
      -- meets scrutinee @Fin (S Z)@ binding @α := Z@; body
      -- @m@ resolves to @Fin α = Fin Z@.  The case typechecks
      -- at the reachable arm's body type — the Dissect
      -- refinement is doing real work.
      "data Nat : *0 { Z : Nat; S : Nat -> Nat };\
      \data Fin (n : Nat) : *0 { FZ : Fin Z; FS : Fin n -> Fin (S n) };\
      \let pred = case FS FZ { FZ -> Z; FS m -> m }"
      ["pred"]

  , accepts "GADT sketch: Iso singleton via separate type decls"
      ("data One : Iso { OneCtor : One };\
       \data Two : Iso { TwoCtor : Two };\
       \data Three : Iso { ThreeCtor : Three };\
       \data Iso : Iso { GetOne : One; GetTwo : Two; GetThree : Three }")
      ["OneCtor", "TwoCtor", "ThreeCtor", "GetOne", "GetTwo", "GetThree"]
    -- NB: there is no @⋮@-shorthand variant of Iso-sep that's
    -- /equivalent/.  'data One ⋮' would desugar to @data One :
    -- One@ (kind One, self-tower) but Iso-sep needs @data One :
    -- Iso@ (kind Iso, member of the singleton family).  The
    -- structures differ: Iso-cute (data Iso { One : One; … }) is
    -- the same-name-at-two-rungs shape; Iso-sep is "Iso is a
    -- /kind/ and each member is a separate type at that kind".
    -- Both elaborate at LVar isoPath at the level layer; the
    -- difference is what's stored in the TyView shape.

  -- --- Refl / propositional equality on Nat ------------------------
  --
  -- The canonical refining GADT.  'Eq' is indexed by two Nats; 'Refl
  -- : Eq a a' refines both indices to coincide.  Hs-codegen end-to-end
  -- on the standard 'data Nat\8942 { Z : Nat; S : Nat -> Nat }' lives in
  -- 'HsSpec'.
  --
  -- Self-typed Nat variant (Iso-style) — each ctor application
  -- yields its own type.  Requires '\8704 a.' on 'S' so the type
  -- variable is bound.  Typecheck-only: the Hs codegen target
  -- can't emit 'Z :: Z' (GHC-56753: ctor used in its own
  -- recursive group); recorded as Scott/codegen follow-up (3)
  -- in PLAN.md.
  --
  -- 'Witness' forces 'Refl' to type 'Eq Z Z' via its ctor's
  -- expected argument type — without it, Refl stays polymorphic
  -- ('Eq a a' for fresh meta 'a').  The meet at the application
  -- site 'ItsZZ Refl' unifies a := Z, so the constructed Refl
  -- is genuinely AT 'Eq Z Z'.
  , acceptsValByHypTwr
      "Refl on Eq Z Z over self-typed Nat\8942 (typecheck-only; Hs codegen gap)"
      "data Nat\8942 { Z : Z; S : \8704 a . a -> S a };\
      \data Eq (a : Nat) (b : Nat) : *0 { Refl : Eq a a };\
      \data Witness : *0 { ItsZZ : Eq Z Z -> Witness };\
      \let rt = ItsZZ Refl"
      ["rt"]

  -- The ⋮ sugar: 'S Nat⋮' desugars to 'S : ∀ a0 : Nat. a0 -> S a0'
  -- via the iso-preserving rule from PLAN.md.  The fresh binder
  -- 'a0' is chosen to avoid collision with anything in scope
  -- (Z, S, Nat all forbidden).
  , acceptsValByHypTwr
      "⋮ sugar on Nat ctors: 'Z⋮; S Nat⋮' desugars to iso-preserving form"
      "data Nat\8942 { Z\8942; S Nat\8942 };\
      \let rt = S Z"
      ["rt"]

  -- Slide-down (Phase A): 'foo' is a value-level let-binding,
  -- referenced in a type position inside 'Box's ctor 'Wrap'.
  -- HypTwr's 'var' previously emitted TyUnbound; now it slides
  -- down the hyper-rise via 'hypTwrEnvValPaths' and emits a
  -- 'TyDeferV' marker.  No meet is forced on the deferred
  -- reference (Wrap is never used at a value site), so
  -- elaboration completes.  Future phases (B+C+D) will reduce
  -- 'TyAppV (TyDefer foo _) args' to its value-level result.
  , acceptsValByHypTwr
      "Slide-down: 'foo' (let-binding on ⋮-typed Nat) in type position emits TyDeferV"
      "data Nat\8942 { Z\8942; S Nat\8942 };\
      \let foo = Z;\
      \data Box : *0 { Wrap : foo -> Box }"
      ["foo"]

  -- Slide-down on a non-⋮ binding.  'flag' is a Bool let-binding
  -- where Bool is declared with explicit '*0' kind (not '⋮' self-
  -- towered).  The slide still emits TyDeferV — Phase A doesn't
  -- check iso-soundness; that's a Phase C concern (where
  -- demote-interpret-promote wouldn't fire for non-⋮ types).
  -- Confirms the slide is type-agnostic: it surfaces ANY let-
  -- binding regardless of whether its type admits the iso bridge.
  , acceptsValByHypTwr
      "Slide-down: non-⋮ let-binding (Bool) in type position emits TyDeferV"
      "data Bool : *0 { T : Bool; F : Bool };\
      \let flag = T;\
      \data Box : *0 { Wrap : flag -> Box }"
      ["flag"]

  -- Phase C: end-to-end demote/interp/promote.  'pickZ Z' appears
  -- in W's expected arg type.  The bridge:
  --   demote (TyConV Z) → VCon "Z" []
  --   interp (pickZ Z) → VCon "Z" []  (case Z dispatches to first arm)
  --   promote (VCon "Z" []) → TyConV "Z" zPath
  -- So 'pickZ Z' normalises to 'Z' at type level.  Then 'W Z'
  -- meets Z's type (Z) against the normalised 'Z' — success.
  -- Without the bridge, this would TyMismatch (TyDeferV vs Z).
  , acceptsBridged
      "Phase C: 'W Z' with W : pickZ Z -> Wit typechecks via demote-interp-promote"
      "data Nat\8942 { Z\8942; S Nat\8942 };\
      \let pickZ = \\n -> case n { Z -> Z; S k -> S Z };\
      \data Wit : *0 { W : pickZ Z -> Wit };\
      \let rt = W Z"
      ["pickZ", "rt"]

  -- Phase D: narrowing.  Uses ⋮-sugar so each ctor value IS its
  -- own type (Z : Z, S : ∀a. a→ S a).  This is the iso-preserving
  -- form required for value-of-let-in-type-position to mean
  -- anything coherent — Z's type is Z (not Nat), so promote(VCon Z)
  -- meets cleanly with Z's type.
  --
  -- W's expected arg type is 'pickZ n' where n is Wit's Nat-kinded
  -- parameter.  At use site, n becomes a fresh meta ?n.
  -- Normalisation can't reduce pickZ ?n (meta arg); standard meet
  -- fails.  The narrowing fallback case-splits ?n on Nat's ctors;
  -- the Z branch yields pickZ Z = Z which matches the LHS;
  -- ?n := Z refinement.  (S branch is currently filtered — Phase
  -- D minimal scope only enumerates nullary ctors; unary needs
  -- fresh sub-meta gen.)
  , acceptsBridgedWithCtors
      "Phase D: 'W Z' with W : pickZ n -> Wit n forces n := Z via narrowing"
      "data Nat\8942 { Z\8942; S Nat\8942 };\
      \let pickZ = \\n -> case n { Z -> Z };\
      \data Wit (n : Nat) : *0 { W : pickZ n -> Wit n };\
      \let rt = W Z"
      ["pickZ", "rt"]
  ]

-- | Helper: parse + elaborate end-to-end via HypLinf → HypTwr; assert
--   the extracted ctor map has exactly the expected keys.  Doesn't
--   pin types (the structural tests in HypTinfSpec / HypTwrSpec
--   already do that); just confirms the program reaches
--   materialisation with the right set of ctors.
accepts :: String -> Text -> [Text] -> (String, IO Bool)
accepts name src wantedCtors = (name, go)
  where
    go = case parseProgram @HypLinf @(Const ()) name src of
      Left e -> fail_ (errorBundlePretty e)
      Right pHypLinf -> case hypLinfRunWith @HypTwr pHypLinf of
        Left lv -> fail_ $ "level layer failed: " <> show lv
        Right (_, pTwr) -> case hypTwrProgram pTwr of
          Left ty -> fail_ $ "type layer failed: " <> show ty
          Right r -> case hypTwrCtorTypes r of
            Left e2 -> fail_ $ "materialize failed: " <> show e2
            Right m
              | Map.keysSet m == Map.keysSet (Map.fromList [(c, ()) | c <- wantedCtors])
                  -> pure True
              | otherwise -> fail_ $
                  "ctor keyset mismatch:\n  want: " <> show wantedCtors
                  <> "\n  got:  " <> show (Map.keys m)
            where _ = hypTwrDataTypes r

-- | Helper: parse OK + elaborate, expect a specific LvErr from the
--   level layer.  Documents that the program is REJECTED today and
--   pins the exact failure, so when the underlying gap is filled
--   (mutual-reference support, etc.) this test will trip and the
--   author will know to flip the marker.
rejectsAtLevel :: String -> Text -> LvErr -> (String, IO Bool)
rejectsAtLevel name src wantErr = (name, go)
  where
    go = case parseProgram @HypLinf @(Const ()) name src of
      Left e -> fail_ $ "parse error (test setup): " <> errorBundlePretty e
      Right pHypLinf -> case hypLinfRunWith @HypTwr pHypLinf of
        Left lv
          | lv == wantErr -> pure True
          | otherwise -> fail_ $
              "level error mismatch:\n  want: " <> show wantErr
              <> "\n  got:  " <> show lv
        Right _ -> fail_ $
          "expected level rejection (" <> show wantErr
          <> "), but program elaborated"

-- | Helper: parse + level OK, expect a specific 'TyErr' from the
--   HypTwr (Tower) layer.  Used for saturation-style rejections
--   that are not level-layer concerns.
rejectsAtType :: String -> Text -> TyErr -> (String, IO Bool)
rejectsAtType name src wantErr = (name, go)
  where
    go = case parseProgram @HypLinf @(Const ()) name src of
      Left e -> fail_ $ "parse error (test setup): " <> errorBundlePretty e
      Right pHypLinf -> case hypLinfRunWith @HypTwr pHypLinf of
        Left lv -> fail_ $ "expected type rejection but level layer failed: " <> show lv
        Right (_, pTwr) -> case hypTwrProgram pTwr of
          Left ty
            | ty == wantErr -> pure True
            | otherwise -> fail_ $
                "type error mismatch:\n  want: " <> show wantErr
                <> "\n  got:  " <> show ty
          Right _ -> fail_ $
            "expected type rejection (" <> show wantErr
            <> "), but program elaborated"

-- | Helper: parse + elaborate, then for each named ctor extract
--   its 'CtorSig' and compare the materialized /refinements/ to
--   the expected pretty representation.  Pinning refinements as
--   pretty text is informative and stable — the pattern-matching
--   machinery will eventually consume these substitutions to
--   compute scrutinee index unifications per arm.
inspectCtorSigs :: String -> Text -> [(Name, [Text])] -> (String, IO Bool)
inspectCtorSigs name src expected = (name, go)
  where
    go = case parseProgram @HypLinf @(Const ()) name src of
      Left e -> fail_ $ "parse error: " <> errorBundlePretty e
      Right pHypLinf -> case hypLinfRunWith @HypTwr pHypLinf of
        Left lv -> fail_ $ "level layer failed: " <> show lv
        Right (_, pTwr) -> case hypTwrProgram pTwr of
          Left ty -> fail_ $ "type layer failed: " <> show ty
          Right r ->
            let subst = hypTwrSubst r
                ctors = hypTwrCtors r
                check (cName, wantPretty) = case Map.lookup cName ctors of
                  Nothing -> fail_ $ "ctor not found: " <> show cName
                  Just tower -> case extractCtorSig subst tower of
                    Nothing -> fail_ $ "extractCtorSig returned Nothing for " <> show cName
                    Just sig -> case traverse (materialize subst) (ctorRefinements sig) of
                      Left e -> fail_ $ "materialize refinement failed: " <> show e
                      Right tys ->
                        let got = map prettyTy tys
                        in if got == wantPretty
                             then pure True
                             else fail_ $
                               "refinement mismatch for " <> show cName
                               <> ":\n  want: " <> show wantPretty
                               <> "\n  got:  " <> show got
            in fmap and (mapM check expected)

-- | Helper: parse directly to 'HypTwr' (bypassing the 'HypLinf'
--   level rail — value-level terms have nothing for the level
--   layer to infer), elaborate, and confirm the resulting 'let'
--   binders match the expected set.  Used for programs containing
--   value-level decls.
-- | Helper: double-parse — first via 'Tree' (to harvest 'Globals'
--   and ctor-paths), then via 'HypTwr' (to elaborate), then run
--   'hypTwrProgramWith' so the slide-down → bridge → interp
--   pipeline (Phases A+B+C) is wired in.  Use for programs whose
--   types involve value-level let-bindings reducible at type level.
acceptsBridged :: String -> Text -> [Name] -> (String, IO Bool)
acceptsBridged name src wantLets = (name, go)
  where
    go = case parseProgram @Tree @(Const ()) name src of
      Left e -> fail_ $ "parse error: " <> errorBundlePretty e
      Right tree ->
        let gs  = extractGlobals tree
            cps = extractCtorPaths tree
        in case parseProgram @HypTwr @(Const ()) name src of
          Left e -> fail_ $ "parse error: " <> errorBundlePretty e
          Right pTwr -> case hypTwrProgramWith gs cps pTwr of
            Left ty -> fail_ $ "HypTwr rejected: " <> show ty
            Right r ->
              let got  = Map.keys (hypTwrValVars r)
                  want = wantLets
              in if got == want
                   then pure True
                   else fail_ $
                     "let-binder set mismatch:\n  want: " <> show want
                     <> "\n  got:  " <> show got

-- | Phase D variant: also injects 'dataCtors' so narrowing can
--   enumerate ctor possibilities for meta arguments.
acceptsBridgedWithCtors :: String -> Text -> [Name] -> (String, IO Bool)
acceptsBridgedWithCtors name src wantLets = (name, go)
  where
    go = case parseProgram @Tree @(Const ()) name src of
      Left e -> fail_ $ "parse error: " <> errorBundlePretty e
      Right tree ->
        let gs     = extractGlobals tree
            cps    = extractCtorPaths tree
            dctors = extractDataCtors tree
        in case parseProgram @HypTwr @(Const ()) name src of
          Left e -> fail_ $ "parse error: " <> errorBundlePretty e
          Right pTwr -> case hypTwrProgramWithCtors gs cps dctors pTwr of
            Left ty -> fail_ $ "HypTwr rejected: " <> show ty
            Right r ->
              let got  = Map.keys (hypTwrValVars r)
                  want = wantLets
              in if got == want
                   then pure True
                   else fail_ $
                     "let-binder set mismatch:\n  want: " <> show want
                     <> "\n  got:  " <> show got

acceptsValByHypTwr :: String -> Text -> [Name] -> (String, IO Bool)
acceptsValByHypTwr name src wantLets = (name, go)
  where
    go = case parseProgram @HypTwr @(Const ()) name src of
      Left e -> fail_ $ "parse error: " <> errorBundlePretty e
      Right pTwr -> case hypTwrProgram pTwr of
        Left ty -> fail_ $ "HypTwr rejected: " <> show ty
        Right r ->
          let got = Map.keys (hypTwrValVars r)
              want = wantLets
          in if got == want
               then pure True
               else fail_ $
                 "let-binder set mismatch:\n  want: " <> show want
                 <> "\n  got:  " <> show got

-- | Helper: parse via 'HypTwr', expect a specific 'TyErr' from the
--   type/match layer.  For value-level programs.
rejectsValAtType :: String -> Text -> TyErr -> (String, IO Bool)
rejectsValAtType name src wantErr = (name, go)
  where
    go = case parseProgram @HypTwr @(Const ()) name src of
      Left e -> fail_ $ "parse error: " <> errorBundlePretty e
      Right pTwr -> case hypTwrProgram pTwr of
        Left ty
          | ty == wantErr -> pure True
          | otherwise -> fail_ $
              "type error mismatch:\n  want: " <> show wantErr
              <> "\n  got:  " <> show ty
        Right _ -> fail_ $
          "expected rejection (" <> show wantErr <> "), elaborated"

fail_ :: String -> IO Bool
fail_ msg = putStrLn ("    " <> msg) >> pure False
