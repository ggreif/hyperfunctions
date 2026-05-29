{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

import Constructor.AST (Tree (..))
import Constructor.Parser (parseProgram)
import Constructor.Path (Path (..), PathStep (..))
import Constructor.Sort (Sort (..))
import qualified HypTinfSpec
import qualified LevelInferSpec
import qualified TinfSpec
import qualified TyProcSpec
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
  putStrLn ""
  putStrLn "type inference:"
  tinfOK <- mapM runInfer TinfSpec.tests
  putStrLn ""
  putStrLn "TyProc.meet apparatus:"
  meetOK <- mapM runInfer TyProcSpec.tests
  putStrLn ""
  putStrLn "B-side type-inference parity:"
  hypTinfOK <- mapM runInfer HypTinfSpec.tests
  if and (parseOK ++ inferOK ++ tinfOK ++ meetOK ++ hypTinfOK) then exitSuccess else exitFailure
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
        [ DataDecl u "Bool" [] (Star u 0)
            [ CtorDecl u "True"  (Var u "Bool")
            , CtorDecl u "False" (Var u "Bool")
            ]
        ]
    )
  , ( "Nat with arrow"
    , "data Nat : *0 { Z : Nat; S : Nat -> Nat }"
    , Prog u
        [ DataDecl u "Nat" [] (Star u 0)
            [ CtorDecl u "Z" (Var u "Nat")
            , CtorDecl u "S" (Arr u (Var u "Nat") (Var u "Nat"))
            ]
        ]
    )
  , ( "nested data"
    , "data Type : *1 { Constr : Type; data Ty2 : Type { Foo : Ty2 } }"
    , Prog u
        [ DataDecl u "Type" [] (Star u 1)
            [ CtorDecl u "Constr" (Var u "Type")
            , DataDecl u "Ty2" [] (Var u "Type")
                [ CtorDecl u "Foo" (Var u "Ty2")
                ]
            ]
        ]
    )
  , ( "right-assoc arrow"
    , "data X : *0 { F : X -> X -> X }"
    , Prog u
        [ DataDecl u "X" [] (Star u 0)
            [ CtorDecl u "F" (Arr u (Var u "X") (Arr u (Var u "X") (Var u "X")))
            ]
        ]
    )
  , ( "polymorphic universe — \8704l. *l"
    , "data Foo : \8704l. *l { c : Foo }"
    , let pBinder = Path [PsProgDecl 0, PsDataAnn]
      in Prog u
        [ DataDecl u "Foo" []
            (ForallLv u "l" pBinder (StarVar u "l" pBinder 0))
            [ CtorDecl u "c" (Var u "Foo")
            ]
        ]
    )
  , ( "polymorphic universe with offset — \8704l. *(l + 2)"
    , "data Bar : \8704l. *(l + 2) { d : Bar }"
    , let pBinder = Path [PsProgDecl 0, PsDataAnn]
      in Prog u
        [ DataDecl u "Bar" []
            (ForallLv u "l" pBinder (StarVar u "l" pBinder 2))
            [ CtorDecl u "d" (Var u "Bar")
            ]
        ]
    )
  , ( "polymorphic universe — keyword 'forall'"
    , "data Q : forall l . *(l + 1) { q : Q }"
    , let pBinder = Path [PsProgDecl 0, PsDataAnn]
      in Prog u
        [ DataDecl u "Q" []
            (ForallLv u "l" pBinder (StarVar u "l" pBinder 1))
            [ CtorDecl u "q" (Var u "Q")
            ]
        ]
    )
  , ( "parametric data — data List a : *0 { Nil : List a }"
    , "data List a : *0 { Nil : List a }"
    , let pa = Path [PsProgDecl 0, PsDataParam 0]
      in Prog u
        [ DataDecl u "List" ["a"] (Star u 0)
            [ CtorDecl u "Nil"
                (App u (Var u "List") (TyParamRef u "a" pa))
            ]
        ]
    )
  , ( "parametric data with arrow ctor — data List a : *0 { Cons : a -> List a -> List a }"
    , "data List a : *0 { Cons : a -> List a -> List a }"
    , let pa = Path [PsProgDecl 0, PsDataParam 0]
      in Prog u
        [ DataDecl u "List" ["a"] (Star u 0)
            [ CtorDecl u "Cons"
                (Arr u (TyParamRef u "a" pa)
                  (Arr u (App u (Var u "List") (TyParamRef u "a" pa))
                          (App u (Var u "List") (TyParamRef u "a" pa))))
            ]
        ]
    )
  , ( "application — three-arg left-assoc f x y z = ((f x) y) z"
    , "data D : *0 { c : f x y z }"
    , Prog u
        [ DataDecl u "D" [] (Star u 0)
            [ CtorDecl u "c"
                (App u
                  (App u
                    (App u (Var u "f") (Var u "x"))
                    (Var u "y"))
                  (Var u "z"))
            ]
        ]
    )
  ]
