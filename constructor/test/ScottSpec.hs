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
