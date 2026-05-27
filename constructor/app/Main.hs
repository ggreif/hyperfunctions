{-# LANGUAGE TypeApplications #-}

module Main (main) where

import Constructor.AST (Tree)
import Constructor.Parser (parseProgram)
import qualified Data.Text.IO as TIO
import System.Environment (getArgs)
import System.Exit (exitFailure)
import Text.Megaparsec (errorBundlePretty)

main :: IO ()
main = do
  args <- getArgs
  src <- case args of
    [path] -> TIO.readFile path
    []     -> TIO.getContents
    _      -> putStrLn "usage: constructor [FILE]" >> exitFailure
  case parseProgram @Tree "<input>" src of
    Left e  -> putStr (errorBundlePretty e) >> exitFailure
    Right t -> print t
