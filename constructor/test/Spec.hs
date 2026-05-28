{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

import Constructor.AST (Tree (..))
import Constructor.Parser (parseProgram)
import Constructor.Sort (Sort (..))
import qualified LevelInferSpec
import Data.Functor.Const (Const (..))
import Data.Text (Text)
import System.Exit (exitFailure, exitSuccess)
import Text.Megaparsec (errorBundlePretty)

-- Convenience alias for the raw tree at @Const ()@ annotations.
type RT (s :: Sort) = Tree (Const ()) s

u :: Const () s
u = Const ()

main :: IO ()
main = do
  putStrLn "parsing:"
  parseOK <- mapM run cases
  putStrLn ""
  putStrLn "level inference:"
  inferOK <- mapM runInfer LevelInferSpec.tests
  if and (parseOK ++ inferOK) then exitSuccess else exitFailure
  where
    runInfer (name, go) = do
      ok <- go
      putStrLn ((if ok then "OK   " else "FAIL ") <> name)
      pure ok

    run :: (String, Text, RT 'SProg) -> IO Bool
    run (name, src, expected) =
      case parseProgram @Tree @(Const ()) name src of
        Left e -> do
          putStrLn ("FAIL " <> name)
          putStr   (errorBundlePretty e)
          pure False
        Right got
          | got == expected -> do
              putStrLn ("OK   " <> name)
              pure True
          | otherwise -> do
              putStrLn ("FAIL " <> name)
              putStrLn ("expected: " <> show expected)
              putStrLn ("got:      " <> show got)
              pure False

cases :: [(String, Text, RT 'SProg)]
cases =
  [ ( "empty program"
    , ""
    , Prog u []
    )
  , ( "single nullary data"
    , "data Bool : *0 { True : Bool; False : Bool }"
    , Prog u
        [ DataDecl u "Bool" (Star u 0)
            [ CtorDecl u "True"  (Var u "Bool")
            , CtorDecl u "False" (Var u "Bool")
            ]
        ]
    )
  , ( "Nat with arrow"
    , "data Nat : *0 { Z : Nat; S : Nat -> Nat }"
    , Prog u
        [ DataDecl u "Nat" (Star u 0)
            [ CtorDecl u "Z" (Var u "Nat")
            , CtorDecl u "S" (Arr u (Var u "Nat") (Var u "Nat"))
            ]
        ]
    )
  , ( "nested data"
    , "data Type : *1 { Constr : Type; data Ty2 : Type { Foo : Ty2 } }"
    , Prog u
        [ DataDecl u "Type" (Star u 1)
            [ CtorDecl u "Constr" (Var u "Type")
            , DataDecl u "Ty2" (Var u "Type")
                [ CtorDecl u "Foo" (Var u "Ty2")
                ]
            ]
        ]
    )
  , ( "right-assoc arrow"
    , "data X : *0 { F : X -> X -> X }"
    , Prog u
        [ DataDecl u "X" (Star u 0)
            [ CtorDecl u "F" (Arr u (Var u "X") (Arr u (Var u "X") (Var u "X")))
            ]
        ]
    )
  ]
