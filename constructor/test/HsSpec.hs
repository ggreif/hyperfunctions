{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

-- | End-to-end codegen test: parse an Ωmegator program, emit
--   Haskell source via the 'Hs' carrier, write to a temp file,
--   run it through @runghc@, and pin the program's stdout.
--
--   The oracle here is GHC.  An Ωmegator program that elaborates
--   AND produces a value should translate to Haskell that GHC
--   accepts AND prints the same logical value when run.  GHC's
--   @-Winaccessible-code@ warnings on unreachable arms are an
--   independent cross-check of our Dissect-side refinement —
--   same observation, different reporter.
module HsSpec (tests) where

import Constructor.Hs (Hs, renderHs)
import Constructor.Parser (parseProgram)
import Data.Functor.Const (Const (..))
import Data.Text (Text)
import qualified Data.Text as T
import System.IO (hPutStr, hClose)
import System.IO.Temp (withSystemTempFile)
import System.Process (readProcessWithExitCode)
import System.Exit (ExitCode (..))
import Text.Megaparsec (errorBundlePretty)

tests :: [(String, IO Bool)]
tests =
  [ runsWith
      "Hs codegen: Bool swap — case T { T -> F; F -> T } prints F"
      -- 'NoImplicitPrelude' in the emitted source lets us use
      -- 'Bool' / 'T' / 'F' freely without clashing with the host
      -- language's identifiers.
      "data Bool : *0 { T : Bool; F : Bool };\
      \let rt = case T { T -> F; F -> T }"
      "F"

  , runsWith
      "Hs codegen: Nat round-trip — case S Z { Z -> Z; S n -> S n } prints S Z"
      "data Nat : *0 { Z : Nat; S : Nat -> Nat };\
      \let rt = case S Z { Z -> Z; S n -> S n }"
      "S Z"

  , runsWith
      "Hs codegen: Fin refining GADT round-trip prints FS FZ"
      -- The load-bearing case: refining GADT, '@'-binder carries
      -- the matched value across.  GHC must accept the translation
      -- (DataKinds / GADT machinery), and the result of running
      -- 'print rt' must be "FS FZ" — same shape as the scrutinee.
      "data Nat : *0 { Z : Nat; S : Nat -> Nat };\
      \data Fin (n : Nat) : *0 { FZ : Fin Z; FS : Fin n -> Fin (S n) };\
      \let rt = case FS FZ { y@FZ -> y; y@FS m -> y }"
      "FS FZ"

  , runsWith
      "Hs codegen: lambda identity — (\\x -> x) T prints T"
      "data Bool : *0 { T : Bool; F : Bool };\
      \let rt = (\\x -> x) T"
      "T"

  , runsWith
      "Hs codegen: lambda flip — (\\x -> case x { T -> F; F -> T }) T prints F"
      -- A lambda whose body is a case.  Demonstrates lambdas
      -- composing with the existing case/dissect machinery.
      "data Bool : *0 { T : Bool; F : Bool };\
      \let rt = (\\x -> case x { T -> F; F -> T }) T"
      "F"

  , runsWith
      "Hs codegen: multi-binder lambda — (\\x y -> x) T F prints T"
      -- Parse-time desugaring: '\\x y -> x' becomes
      -- '\\x -> \\y -> x'.  Left-associative application then
      -- consumes T at outer, F at inner; const-fst returns T.
      "data Bool : *0 { T : Bool; F : Bool };\
      \let rt = (\\x y -> x) T F"
      "T"

  , runsWith
      "Hs codegen: fib on Nat\8942 base case — fib Z prints Z"
      -- fib(0) = 0: hits the outer 'Z -> Z' arm immediately, no
      -- recursion fired.  Validates that the base case terminates
      -- and the (now-recursive) let doesn't loop on a Z input.
      "data Nat\8942 { Z : Nat; S : Nat -> Nat };\
      \let add = \\x y -> case x { Z -> y; S n -> S (add n y) };\
      \let fib = \\n -> case n { Z -> Z; S k -> case k { Z -> S Z; S m -> add (fib (S m)) (fib m) } };\
      \let rt = fib Z"
      "Z"

  , runsWith
      "Hs codegen: fib on Nat\8942 second base — fib (S Z) prints S Z"
      -- fib(1) = 1: hits the @S k@ outer arm, inner @Z -> S Z@
      -- arm.  Two-level pattern descent, still no recursion.
      "data Nat\8942 { Z : Nat; S : Nat -> Nat };\
      \let add = \\x y -> case x { Z -> y; S n -> S (add n y) };\
      \let fib = \\n -> case n { Z -> Z; S k -> case k { Z -> S Z; S m -> add (fib (S m)) (fib m) } };\
      \let rt = fib (S Z)"
      "S Z"

  , runsWith
      "Hs codegen: fib on Nat\8942 via recursive let — fib (S (S (S Z))) prints S (S Z)"
      -- The canonical recursive function on a self-towered Nat.
      -- Uses recursive 'let' (HypTwr's valDecl pre-binds the name
      -- to a meta tower, unifies against the body's actual type
      -- after elaboration), nested case for the @n = S (S _)@
      -- step, and value-level lambda + application throughout.
      --
      -- Defines 'add' first (also recursive); fib(3) = 2 = S (S Z).
      "data Nat\8942 { Z : Nat; S : Nat -> Nat };\
      \let add = \\x y -> case x { Z -> y; S n -> S (add n y) };\
      \let fib = \\n -> case n { Z -> Z; S k -> case k { Z -> S Z; S m -> add (fib (S m)) (fib m) } };\
      \let rt = fib (S (S (S Z)))"
      "S (S Z)"

  , runsWith
      "Hs codegen: Refl on Eq over Nat\8942 — case Refl { Refl -> Z } prints Z"
      -- Equality-witness GADT indexed by two 'Nat\8942's.  'Refl's
      -- type is 'Eq a a' — the two indices coincide.  Scrutinee
      -- 'Refl' has fresh 'Eq a a'; pattern-match against 'Refl'
      -- refines the meta (no-op for matching identity), body
      -- returns 'Z'.
      "data Nat\8942 { Z : Nat; S : Nat -> Nat };\
      \data Eq (a : Nat) (b : Nat) : *0 { Refl : Eq a a };\
      \let rt = case Refl { Refl -> Z }"
      "Z"

  -- Note: 'data Nat\8942 { Z : Z; S : a -> S a }' (Iso-style self-
  -- typing where each value IS its own type) parses and type-
  -- checks in the constructor language, but the Hs codegen
  -- emits 'Z :: Z' which GHC rejects with GHC-56753 ("Data
  -- constructor 'Z' cannot be used here (it is defined and
  -- used in the same recursive group)").  A self-typing-aware
  -- Hs codegen would need to erase the self-typing to a flat
  -- 'data Nat where Z :: Nat; S :: Nat -> Nat' at the Haskell
  -- target — losing the type-level distinction but preserving
  -- value-level behaviour.  Recorded in PLAN.md; not exercised
  -- here pending that codegen extension.
  ]

-- | Parse via the 'Hs' carrier, run via @runghc@, assert the
--   stdout matches the expected output (after trimming).
runsWith :: String -> Text -> String -> (String, IO Bool)
runsWith name src expected = (name, go)
  where
    go = case parseProgram @Hs @(Const ()) name src of
      Left e -> failR $ "parse error: " <> errorBundlePretty e
      Right hsProg -> do
        let src' = renderHs hsProg
        withSystemTempFile "omegator-demo.hs" $ \fp h -> do
          hPutStr h src'
          hClose h
          (ec, out, err) <- readProcessWithExitCode "runghc" [fp] ""
          case ec of
            ExitFailure code -> failR $
              "runghc failed (exit " <> show code <> "):\n"
              <> "  stderr: " <> err <> "\n"
              <> "  emitted source was:\n" <> indent src'
            ExitSuccess ->
              let trimmed = T.unpack (T.strip (T.pack out))
              in if trimmed == expected
                   then pure True
                   else failR $
                     "stdout mismatch:\n"
                     <> "  want: " <> show expected <> "\n"
                     <> "  got:  " <> show trimmed <> "\n"
                     <> "  emitted source was:\n" <> indent src'

    failR msg = putStrLn ("    " <> msg) >> pure False

    indent = unlines . map ("      " <>) . lines
