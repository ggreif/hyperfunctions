{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

-- | End-to-end Scott codegen test: parse an Ωmegator program,
--   emit Scott-encoded Haskell via 'Constructor.Scott', run
--   through @runghc@, pin the program's stdout.
--
--   Limited to nullary-ctor demos (Bool, Iso) for this first
--   carrier.  Captured-args (Nat S) and refining GADTs (Fin)
--   need extensions and will land in follow-up carrier
--   commits — the Scott encoding /works/ for them (see the
--   hand-coded /tmp/scott-{nat,fin}.hs experiments), but the
--   carrier itself doesn't generate that shape yet.
module ScottSpec (tests) where

import Constructor.Parser (parseProgram)
import Constructor.Scott (Scott, renderScott)
import Data.Functor.Const (Const (..))
import Data.Text (Text)
import qualified Data.Text as T
import System.Exit (ExitCode (..))
import System.IO (hClose, hPutStr)
import System.IO.Temp (withSystemTempFile)
import System.Process (readProcessWithExitCode)
import Text.Megaparsec (errorBundlePretty)

tests :: [(String, IO Bool)]
tests =
  [ runsWith
      "Scott codegen: Bool swap — case T { T -> F; F -> T } prints F"
      "data Bool : *0 { T : Bool; F : Bool };\
      \let rt = case T { T -> F; F -> T }"
      "F"

  , runsWith
      "Scott codegen: Iso One rotates — case One { … } prints Two"
      "data Iso : Iso { One : One; Two : Two; Three : Three };\
      \let rt = case One { One -> Two; Two -> Three; Three -> One }"
      "Two"

  , runsWith
      "Scott codegen: Nat predecessor — case S Z { Z -> Z; S n -> n } prints Z"
      -- Captured-arg ctor: S's branch type is @(Nat' -> x)@.
      -- The arm @S n -> n@ binds @n@ at the captured arg's type
      -- (Nat') and the body returns it.
      "data Nat : *0 { Z : Nat; S : Nat -> Nat };\
      \let rt = case S Z { Z -> Z; S n -> n }"
      "Z"

  , runsWith
      "Scott codegen: existential round-trip — case Pack T { Pack x -> Pack x }"
      -- Existential ctor: Pack's branch type wraps with
      -- @forall m.@.  The arm rebuilds via the same ctor; the
      -- existential is opaque from outside, so showFoo just
      -- says "Pack <existential>".
      "data Bool : *0 { T : Bool };\
      \data Foo : *0 { Pack : \8707 m . m -> Foo };\
      \let rt = case Pack T { Pack x -> Pack x }"
      "(Pack <existential>)"

  , runsWith
      "Scott codegen: Maybe parametric — non-refining"
      -- Parametric (a) data type with no per-ctor refinement.
      -- Scott uses an index-parameterised x but every branch
      -- lands at the SAME index (the param), so it degenerates
      -- to "regular Scott with a type variable carried through".
      "data Bool : *0 { T : Bool };\
      \data Maybe (a : *0) : *0 { Nothing : Maybe a; Just : a -> Maybe a };\
      \let rt = case Just T { Nothing -> Nothing; Just x -> Just x }"
      "(Just <unrecognised a>)"

  , runsWith
      "Scott codegen: Fin refining GADT — indexed eliminator"
      -- The load-bearing test for the indexed-elim regime.  Uses
      -- DataKinds promotion of Nat ctors (Z, S) as Fin's index;
      -- Fin's eliminator is @forall (x :: Nat -> Type). x Z -> …@.
      -- The Haskell @data Nat = Z | S Nat@ provides the kind;
      -- the Scott @newtype Nat'@ provides runtime; both coexist.
      "data Nat : *0 { Z : Nat; S : Nat -> Nat };\
      \data Fin (n : Nat) : *0 { FZ : Fin Z; FS : Fin n -> Fin (S n) };\
      \let rt = case FS FZ { FZ -> FZ; FS m -> FS m }"
      "(FS FZ)"

  , runsWith
      "Scott codegen: Bush non-regular nested data"
      -- Non-regular: ConsB's tail has type Bush (Bush a) — the
      -- type parameter deepens at each recursive position.  This
      -- is the canonical witness for the 'emitNonRefining' regime
      -- (regular Scott with the type variables threaded through).
      -- Both arms return NilB at type Bush Bool, so the result is
      -- the empty Bush.
      "data Bool : *0 { T : Bool };\
      \data Bush (a : *0) : *0 { NilB : Bush a; ConsB : a -> Bush (Bush a) -> Bush a };\
      \let rt = case ConsB T NilB { NilB -> NilB; ConsB x xs -> NilB }"
      "NilB"

  , runsWith
      "Scott codegen: Bush extracts deeper-typed tail"
      -- Genuinely exercises the non-regular deepening: the ConsB
      -- arm returns xs, whose type is Bush (Bush Bool) — strictly
      -- deeper than the scrutinee's Bush Bool.  Both arms must
      -- agree at the deeper type, which NilB's polymorphism
      -- supplies.
      "data Bool : *0 { T : Bool };\
      \data Bush (a : *0) : *0 { NilB : Bush a; ConsB : a -> Bush (Bush a) -> Bush a };\
      \let rt = case ConsB T NilB { NilB -> NilB; ConsB x xs -> xs }"
      "NilB"

  , runsWith
      "Scott codegen: lambda identity — (\\x -> x) T"
      -- Plainest lambda case in Scott land.  No closures over the
      -- Scott-encoded data: just a Haskell lambda emitted verbatim
      -- and applied to a Scott-encoded ctor.  showRt on the result
      -- (a Bool-typed value) prints "T".
      "data Bool : *0 { T : Bool; F : Bool };\
      \let rt = (\\x -> x) T"
      "T"

  , runsWith
      "Scott codegen: fib on Nat\8942 base case — fib Z"
      "data Nat\8942 { Z : Nat; S : Nat -> Nat };\
      \let add = \\x y -> case x { Z -> y; S n -> S (add n y) };\
      \let fib = \\n -> case n { Z -> Z; S k -> case k { Z -> S Z; S m -> add (fib (S m)) (fib m) } };\
      \let rt = fib Z"
      "Z"

  , runsWith
      "Scott codegen: fib on Nat\8942 second base — fib (S Z)"
      "data Nat\8942 { Z : Nat; S : Nat -> Nat };\
      \let add = \\x y -> case x { Z -> y; S n -> S (add n y) };\
      \let fib = \\n -> case n { Z -> Z; S k -> case k { Z -> S Z; S m -> add (fib (S m)) (fib m) } };\
      \let rt = fib (S Z)"
      "(S Z)"

  , runsWith
      "Scott codegen: fib on Nat\8942 — fib (S (S (S Z)))"
      -- Recursive let + multi-pattern-desugar + nested case +
      -- value-level application chain, all routed through the
      -- Scott-encoded Nat.  Same expectation as the Hs analog:
      -- fib(3) = 2 = S (S Z).  showRt prints "(S (S Z))" — the
      -- Scott carrier's parenthesised form for a non-nullary ctor.
      "data Nat\8942 { Z : Nat; S : Nat -> Nat };\
      \let add = \\x y -> case x { Z -> y; S n -> S (add n y) };\
      \let fib = \\n -> case n { Z -> Z; S k -> case k { Z -> S Z; S m -> add (fib (S m)) (fib m) } };\
      \let rt = fib (S (S (S Z)))"
      "(S (S Z))"
  ]

runsWith :: String -> Text -> String -> (String, IO Bool)
runsWith name src expected = (name, go)
  where
    go = case parseProgram @Scott @(Const ()) name src of
      Left e -> failR $ "parse error: " <> errorBundlePretty e
      Right scProg -> do
        let src' = renderScott scProg
        withSystemTempFile "omegator-scott.hs" $ \fp h -> do
          hPutStr h src'
          hClose h
          (ec, out, err) <- readProcessWithExitCode "runghc" [fp] ""
          case ec of
            ExitFailure code -> failR $
              "runghc failed (exit " <> show code <> "):\n"
              <> "  stderr: " <> err <> "\n"
              <> "  emitted source:\n" <> indent src'
            ExitSuccess ->
              let trimmed = T.unpack (T.strip (T.pack out))
              in if trimmed == expected
                   then pure True
                   else failR $
                     "stdout mismatch:\n"
                     <> "  want: " <> show expected <> "\n"
                     <> "  got:  " <> show trimmed <> "\n"
                     <> "  emitted source:\n" <> indent src'

    failR msg = putStrLn ("    " <> msg) >> pure False

    indent = unlines . map ("      " <>) . lines
