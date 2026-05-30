{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

-- | Axiomatic Build → Dissect → Build round-trip tests.
--
--   Each program builds a ctor-shaped value, dissects it with a
--   covering case, and rebuilds the scrutinee shape arm-by-arm.
--   The /axiomatic/ content the suite captures is:
--
--     1. **What can be built can be dissected.**  Every Built
--        value matches at least one arm (no inexhaustive matches).
--
--     2. **What is dissected can be rebuilt to the /same type/.**
--        The case as a whole types at the scrutinee's type — each
--        arm's body, after refinement, produces a value at that
--        type.  For refining GADTs (real Fin / Expr / Refl) some
--        arms become unreachable; the elaborator should accept
--        them anyway and the round-trip should still preserve
--        type at the reachable arm(s).
--
--   At this commit HypTwr does scope-only elaboration for value-
--   level terms — the tests confirm the programs parse + elaborate
--   without scope errors and that the expected 'let' binders land
--   in 'hypTwrValVars'.  When Build / Dissect type-checking lands
--   (next segment), the same programs will exercise real
--   refinement unification; tests that today are weak (scope-only)
--   strengthen automatically because 'hypTwrProgram' starts
--   inspecting types as well as scope.
module AxiomsSpec (tests) where

import Constructor.HypTwr (HypTwr, HypTwrResult (..), hypTwrProgram)
import Constructor.Parser (parseProgram)
import Constructor.Syntax (Name)
import Data.Functor.Const (Const (..))
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Text.Megaparsec (errorBundlePretty)

tests :: [(String, IO Bool)]
tests =
  [ -- --- Non-refining round-trips -----------------------------------
    --
    -- Bool and Nat: no per-ctor refinement; every arm's pattern
    -- and body share the same shape, so Build → Dissect → Build is
    -- trivially type-preserving.  Scope axioms:
    --
    --   * Built value's name is bound for the case to consume.
    --   * Each arm's pattern-introduced binder is in scope in its
    --     body and resolves through HypTwr.
    --   * Rebuilding the same ctor shape on the RHS doesn't escape
    --     the arm — bound names are arm-local, but the rebuilt
    --     value's typing context is the case's outer scope.

    roundTripVia "Bool round-trip: case T { T -> T; F -> F }"
      "data Bool : *0 { T : Bool; F : Bool };\
      \let rt = case T { T -> T; F -> F }"
      ["rt"]

  , roundTripVia "Nat round-trip: case S Z { Z -> Z; S n -> S n }"
      -- Round-trip preserves ctor shape under FS-binding.  The
      -- pattern binder 'n' flows from the FS pattern into the FS
      -- argument position on the RHS; the rebuilt value has the
      -- same Nat shape the scrutinee had.
      "data Nat : *0 { Z : Nat; S : Nat -> Nat };\
      \let rt = case S Z { Z -> Z; S n -> S n }"
      ["rt"]

    -- --- Refining round-trips -----------------------------------------
    --
    -- Real Fin: per-ctor result refinement.  The 'FZ' arm refines
    -- 'n' to 'Z'; the 'FS m' arm refines 'n' to 'S m' with 'm' a
    -- fresh existential.  For a scrutinee of type 'Fin (S Z)':
    --
    --   * The 'FZ' arm is /unreachable/ (refinement clash:
    --     'S Z != Z'), but the elaborator accepts the arm —
    --     unreachability is a coverage observation, not a type
    --     error.
    --   * The 'FS m' arm is reachable; 'm := Z' instantiates the
    --     existential.  Rebuilding 'FS m' yields 'Fin (S m) =
    --     Fin (S Z)' — same type as the scrutinee.
    --
    -- Today: scope-only.  When pat refinement lands, the test
    -- strengthens automatically into a genuine refinement axiom.

  , roundTripVia "Fin round-trip: case FS FZ { FZ -> FZ; FS m -> FS m }"
      -- Refining GADT round-trip — the load-bearing case.
      -- Scrutinee @FS FZ@ has type @Fin (S Z)@.  The @FZ@ arm's
      -- pattern matches @Fin Z@; refinement clashes with the
      -- scrutinee's @Fin (S Z)@, so HypTwr marks the arm
      -- /unreachable/ and skips its body when meeting per-arm
      -- result types.  The @FS m@ arm refines @m@ to @Z@ and
      -- its body @FS m@ rebuilds at @Fin (S Z)@ — same type
      -- as the scrutinee.  The axiom holds.
      "data Nat : *0 { Z : Nat; S : Nat -> Nat };\
      \data Fin (n : Nat) : *0 { FZ : Fin Z; FS : Fin n -> Fin (S n) };\
      \let rt = case FS FZ { FZ -> FZ; FS m -> FS m }"
      ["rt"]

    -- --- Typed-AST round-trip ----------------------------------------
    --
    -- Real Expr from GadtSpec: 'Lit : Expr T', 'Pair : Expr T ->
    -- Expr F -> Expr F'.  Round-tripping 'Lit' through its arm
    -- preserves the 'Expr T' result type.  The 'Pair l r' arm's
    -- pattern binders 'l' and 'r' flow into the rebuilt 'Pair l r'.

  , roundTripVia "Expr round-trip: case Lit { Lit -> Lit }"
      "data Bool : *0 { T : Bool; F : Bool };\
      \data Expr (a : Bool) : *0 { Lit : Expr T; Pair : Expr T -> Expr F -> Expr F };\
      \let rt = case Lit { Lit -> Lit; Pair l r -> Lit }"
      ["rt"]

    -- --- Coverage axiom: every Built value matches an arm --------
    --
    -- This test will tighten when coverage checking is added.
    -- Today it just confirms that all reachable arms parse + scope.
    -- A future commit lands inexhaustive-match detection on top.

  , roundTripVia "Coverage: every Bool-ctor has a covering arm"
      "data Bool : *0 { T : Bool; F : Bool };\
      \let cov = case T { T -> F; F -> T }"
      ["cov"]

    -- --- Weird-class (self-towering / singleton family) -----------
    --
    -- Singleton self-towering data have each ctor's annotation
    -- equal to its own name (or another sibling's): the value
    -- 'One' has type 'One', not 'Iso'.  At case time the
    -- scrutinee's type is fixed by /which/ ctor built it, so
    -- only that arm's pattern meets the scrutinee — every other
    -- arm clashes on TyMismatch and is filtered.  Reachable
    -- arms agree on their rebuild type (= scrutinee's type) by
    -- construction.
    --
    -- The covering-space framing's content surfaces here: at a
    -- nullary self-towering parent, the parent and each ctor
    -- inhabit the same parametric-level fibre, and the
    -- value-level Build / Dissect pas-de-deux is just the
    -- TyConV identity check.

  , roundTripVia "Weird round-trip: case Level0 { Level0 -> Level0 }"
      -- The minimal Weird-class case: one ctor, one arm.  Scrut
      -- @Level0 : Weird@; pat @Level0@ tower @Weird@ meets;
      -- body @Level0@ rebuilds at @Weird@ — same type as the
      -- scrutinee.
      "data Weird : Weird { Level0 : Weird };\
      \let rt = case Level0 { Level0 -> Level0 }"
      ["rt"]

  , roundTripVia "Iso round-trip: case One { One -> One; Two -> Two; Three -> Three }"
      -- The Iso-cute singleton: each ctor has its own type.
      -- For scrut @One : One@, arm @One@ tower @One@ meets;
      -- arms @Two@ and @Three@ have towers @Two@ / @Three@ —
      -- both clash with @One@, both filtered.  Reachable arm's
      -- body @One@ rebuilds at @One@ = scrutinee's type.
      "data Iso : Iso { One : One; Two : Two; Three : Three };\
      \let rt = case One { One -> One; Two -> Two; Three -> Three }"
      ["rt"]

  , roundTripVia "Swap round-trip: case Left { Left -> Left; Right -> Right }"
      -- Swap's twist: @Left@'s annotation is @Right@ (and vice
      -- versa).  So @Left@ /builds/ a value of type @Right@.
      -- Scrut @Left : Right@; arm @Left@'s pat tower is also
      -- @Right@ (matching the building-rule); arm @Right@'s pat
      -- tower is @Left@ — clashes with @Right@, filtered.
      -- Body @Left@ rebuilds at @Right@.  The round-trip's
      -- typed shape is /the swap target/, not the matched ctor.
      "data Swap : Swap { Left : Right; Right : Left };\
      \let rt = case Left { Left -> Left; Right -> Right }"
      ["rt"]

  , roundTripVia "Mirror round-trip: case Cup { Cup -> Cup; Fridge -> Fridge; Plate -> Plate }"
      -- The universe-polymorphic Iso: same structure as Iso
      -- but the parent's kind is @∀l. *l@ rather than a
      -- self-referential TyConRef.  Cup/Fridge/Plate live at
      -- the parametric level the parent's ∀ introduces.  At
      -- value level the type-checker doesn't care about the
      -- parent's level shape — the case operates on TyConV
      -- identity of each ctor's annotation, exactly as in Iso.
      "data Mirror : \8704l. *l { Cup : Cup; Fridge : Fridge; Plate : Plate };\
      \let rt = case Cup { Cup -> Cup; Fridge -> Fridge; Plate -> Plate }"
      ["rt"]
  ]

-- | Parse → 'HypTwr' → expect success.  Verifies that all expected
--   'let' binders land in 'hypTwrValVars'.  Once Build / Dissect
--   type-checking lands, the binder map will carry types as well
--   (currently '()'), and this helper will additionally inspect
--   the types via a richer expected-value parameter.
roundTripVia :: String -> Text -> [Name] -> (String, IO Bool)
roundTripVia name src wantLets = (name, go)
  where
    go = case parseProgram @HypTwr @(Const ()) name src of
      Left e -> fail_ $ "parse error: " <> errorBundlePretty e
      Right pTwr -> case hypTwrProgram pTwr of
        Left ty -> fail_ $ "HypTwr rejected: " <> show ty
        Right r ->
          let got = Map.keys (hypTwrValVars r)
          in if got == wantLets
               then pure True
               else fail_ $
                 "let-binder set mismatch:\n  want: " <> show wantLets
                 <> "\n  got:  " <> show got

    fail_ msg = putStrLn ("    " <> msg) >> pure False
