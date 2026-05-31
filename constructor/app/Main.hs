{-# LANGUAGE TypeApplications #-}

module Main (main) where

import Constructor.HypTwr
  ( HypTwr
  , HypTwrResult (..)
  , hypTwrCtorTypes
  , hypTwrProgram
  )
import Constructor.Hs (Hs, renderHs)
import Constructor.Parser (parseProgram)
import Constructor.Scott (Scott, renderScott)
import Constructor.Tower (horizontal)
import Constructor.TyExpr (prettyTy)
import Constructor.TyProc (materialize)
import Data.Functor.Const (Const)
import qualified Data.Map.Strict as Map
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Environment (getArgs)
import System.Exit (exitFailure)
import Text.Megaparsec (errorBundlePretty)

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--hs", path]    -> emitHs    path
    ["--scott", path] -> emitScott path
    ["--types", path] -> emitTypes path
    [path]            -> emitScott path
    _ -> putStrLn "usage: constructor [--hs|--scott|--types] FILE" >> exitFailure

emitHs, emitScott, emitTypes :: FilePath -> IO ()

emitHs path = do
  src <- TIO.readFile path
  case parseProgram @Hs @(Const ()) "<input>" src of
    Left e  -> putStr (errorBundlePretty e) >> exitFailure
    Right p -> putStr (renderHs p)

emitScott path = do
  src <- TIO.readFile path
  case parseProgram @Scott @(Const ()) "<input>" src of
    Left e  -> putStr (errorBundlePretty e) >> exitFailure
    Right p -> putStr (renderScott p)

emitTypes path = do
  src <- TIO.readFile path
  case parseProgram @HypTwr @(Const ()) "<input>" src of
    Left e  -> putStr (errorBundlePretty e) >> exitFailure
    Right p -> case hypTwrProgram p of
      Left ty -> putStrLn ("HypTwr error: " <> show ty) >> exitFailure
      Right r -> do
        case hypTwrCtorTypes r of
          Left e  -> putStrLn ("ctor materialise error: " <> show e)
          Right m -> mapM_ printNameType (Map.toList m)
        putStrLn "--"
        mapM_ (printBinder r) (Map.toList (hypTwrValVars r))
  where
    printNameType (name, ty) =
      putStrLn $ T.unpack name <> " :: " <> T.unpack (prettyTy ty)
    printBinder r (name, tower) =
      case materialize (hypTwrSubst r) (horizontal tower) of
        Left e  -> putStrLn $ T.unpack name <> " :: <materialize error: " <> show e <> ">"
        Right t -> putStrLn $ T.unpack name <> " :: " <> T.unpack (prettyTy t)
