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
