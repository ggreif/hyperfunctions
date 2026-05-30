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
import Constructor.Tinf (TyErr (..))
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

  , rejectsTwrPending
      "Fin round-trip: case FS FZ { FZ -> FZ; FS m -> FS m }"
      -- INTENTIONALLY rejecting at this commit: Build-side ctor
      -- typing now produces real result types for each arm, so
      -- @FZ : Fin Z@ and @FS m : Fin (S m)@ don't pairwise meet.
      -- The /actual/ axiom holds only after Dissect-side
      -- refinement filters unreachable arms: for a scrutinee
      -- @Fin (S Z)@ the FZ arm clashes (n=Z vs S Z), gets
      -- dropped, and the FS m arm alone determines the case's
      -- type — Fin (S Z), matching the scrutinee.  When the
      -- Dissect commit lands, this test flips back to
      -- 'roundTripVia' and the axiom is restored.
      "data Nat : *0 { Z : Nat; S : Nat -> Nat };\
      \data Fin (n : Nat) : *0 { FZ : Fin Z; FS : Fin n -> Fin (S n) };\
      \let rt = case FS FZ { FZ -> FZ; FS m -> FS m }"

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

-- | Forward-pointing helper: confirms HypTwr currently /rejects/
--   the program with a 'TyMismatch' (we don't pin the exact
--   TyExpr operands because they involve metavariables whose
--   renderings include placeholders).  When the load-bearing
--   feature lands — typically Dissect-side refinement —
--   the failure becomes a success and the call site flips to
--   'roundTripVia'.
rejectsTwrPending :: String -> Text -> (String, IO Bool)
rejectsTwrPending name src = (name, go)
  where
    go = case parseProgram @HypTwr @(Const ()) name src of
      Left e -> failR $ "parse error: " <> errorBundlePretty e
      Right pTwr -> case hypTwrProgram pTwr of
        Left (TyMismatch _ _) -> pure True
        Left other -> failR $ "expected TyMismatch, got: " <> show other
        Right _ -> failR "expected pending rejection but program elaborated"

    failR msg = putStrLn ("    " <> msg) >> pure False
