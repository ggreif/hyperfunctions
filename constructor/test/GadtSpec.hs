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

import Constructor.HypLinf (HypLinf, hypLinfRunWith)
import Constructor.HypTwr (HypTwr, HypTwrResult (..), hypTwrCtorTypes, hypTwrProgram)
import Constructor.LevelInfer (LvErr (..))
import Constructor.Parser (parseProgram)
import Data.Functor.Const (Const (..))
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Text.Megaparsec (errorBundlePretty)

tests :: [(String, IO Bool)]
tests =
  -- --- Reachable today -------------------------------------------
  --
  -- WARNING — none of these are 'real' GADTs.  The parametric
  -- variants below have the same ctor /names/ as Fin / Expr but
  -- LACK both arrow-kinded data declarations (e.g. @data Fin :
  -- Nat -> *@) and per-ctor result-type refinement.  Real Fin
  -- needs @FZ : Fin (S n)@ and @FS : Fin n -> Fin (S n)@ — each
  -- ctor's result is the parent applied to a /specific/ index
  -- that may differ from other ctors.  The fakes here have
  -- @FZ : Fin n@ for ANY n (so @Fin Z@, which should be empty,
  -- is inhabited).  Kept as 'baseline shape' tests for when the
  -- real GADT machinery lands; renamed to make the falseness
  -- explicit.
  [ accepts "GADT sketch: fake-Fin (parametric, NOT a real GADT — no result refinement)"
      "data Nat : *0 { Z : Nat; S : Nat -> Nat };\
      \data Fin n : *0 { FZ : Fin n; FS : Fin n -> Fin n }"
      ["FZ", "FS", "Z", "S"]
  , accepts "GADT sketch: fake-Expr (parametric, NOT a real typed-AST GADT)"
      "data Expr a : *0 { Lit : a -> Expr a; App : Expr a -> Expr a -> Expr a }"
      ["Lit", "App"]
  , accepts "GADT sketch: Iso flat (Weird-style; all ctors : Iso)"
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
  , accepts "GADT sketch: kind-annotated parameter (a : Nat) — surface syntax"
      -- 'data Fin (n : Nat) : *0' with kind annotation on n.  The
      -- kind expression is parsed and validated but not yet
      -- semantically consumed (HypLinf / HypTinf / HypTwr all
      -- destructure as @(name, _kindMaybe)@ today).  Step 1 of
      -- the GADT roadmap — surface only; per-ctor refinement
      -- comes later.
      "data Nat : *0 { Z : Nat; S : Nat -> Nat };\
      \data Fin (n : Nat) : *0 { FZ : Fin n; FS : Fin n -> Fin n }"
      ["FZ", "FS", "Z", "S"]
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

  -- --- Doubly blocked: arrow-kinded data + GADT refinement ------
  --
  -- Real Fin / Expr / Vec aren't even parseable today; they need
  -- two orthogonal features beyond mutual references:
  --
  -- 1. **Arrow-kinded data declarations.**  Real Fin is declared
  --    @data Fin : Nat -> *0 where ...@ — its kind is an arrow,
  --    not a flat universe.  Today the kind-annotation grammar
  --    only accepts @*n@, @∀l. *(l + k)@, or a self-referential
  --    'TyConRef'.  Adding arrow kinds requires both parser
  --    surface (post-':' expression grammar gains '->'-shapes)
  --    and elaborator semantics (HypLinf's predLv treatment of
  --    arrow-kinded data; HypTinf / HypTwr's view of an
  --    arrow-kinded parent for kind coherence).
  --
  -- 2. **Per-ctor result-type refinement.**  Real Fin's @FZ : Fin
  --    (S n)@ has a result type that DIFFERS from the parent
  --    declaration's name applied to its formal parameters.
  --    Today ctorDecl just stores the parsed annotation verbatim;
  --    there's no machinery to enforce "ctor returns the parent
  --    tycon with the right number of arguments" /nor/ to refine
  --    the index inside a pattern-match arm.  Refinement-aware
  --    meet (the bind-direction guard via TyProc-meta identity,
  --    prepared by the v0.1.0 TyView → TyProc lift) is the
  --    substrate; the elaborator-side work is the per-arm scope
  --    where the refinement applies.
  --
  -- Sketches of what real Fin / Expr would look like (NOT
  -- runnable today; here for forward documentation):
  --
  --     data Fin : Nat -> *0 where
  --       FZ : Fin (S n)
  --       FS : Fin n -> Fin (S n)
  --
  --     data Expr : *0 -> *0 where
  --       Lit  : Int  -> Expr Int
  --       If   : Expr Bool -> Expr a -> Expr a -> Expr a
  --       App  : Expr (a -> b) -> Expr a -> Expr b
  --
  --     data (~) : forall l. *l -> *l -> *l where
  --       Refl : a ~ a
  --
  -- All three drop into place once arrow-kinded data + per-ctor
  -- result refinement lands, with no further Tower-level
  -- accommodations needed (the refinement-vs-existential
  -- distinction is already operational through TyProc identity).
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

fail_ :: String -> IO Bool
fail_ msg = putStrLn ("    " <> msg) >> pure False
