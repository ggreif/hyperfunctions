{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

import Constructor.AST (Tree (..))
import Constructor.Parser (parseProgram)
import Constructor.Sort (Sort (..))
import Data.Text (Text)
import System.Exit (exitFailure, exitSuccess)
import Text.Megaparsec (errorBundlePretty)

main :: IO ()
main = do
  results <- mapM run cases
  if and results then exitSuccess else exitFailure
  where
    run :: (String, Text, Tree 'SProg) -> IO Bool
    run (name, src, expected) =
      case parseProgram @Tree name src of
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

cases :: [(String, Text, Tree 'SProg)]
cases =
  [ ( "empty program"
    , ""
    , Prog []
    )
  , ( "single nullary data"
    , "data Bool : *0 { True : Bool; False : Bool }"
    , Prog
        [ DataDecl "Bool" (Star 0)
            [ CtorDecl "True"  (Var "Bool")
            , CtorDecl "False" (Var "Bool")
            ]
        ]
    )
  , ( "Nat with arrow"
    , "data Nat : *0 { Z : Nat; S : Nat -> Nat }"
    , Prog
        [ DataDecl "Nat" (Star 0)
            [ CtorDecl "Z" (Var "Nat")
            , CtorDecl "S" (Arr (Var "Nat") (Var "Nat"))
            ]
        ]
    )
  , ( "nested data"
    , "data Type : *1 { Constr : Type; data Ty2 : Type { Foo : Ty2 } }"
    , Prog
        [ DataDecl "Type" (Star 1)
            [ CtorDecl "Constr" (Var "Type")
            , DataDecl "Ty2" (Var "Type")
                [ CtorDecl "Foo" (Var "Ty2")
                ]
            ]
        ]
    )
  , ( "right-assoc arrow"
    , "data X : *0 { F : X -> X -> X }"
    , Prog
        [ DataDecl "X" (Star 0)
            [ CtorDecl "F" (Arr (Var "X") (Arr (Var "X") (Var "X")))
            ]
        ]
    )
  ]
