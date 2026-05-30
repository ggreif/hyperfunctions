{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

import Constructor.AST (Tree (..))
import Constructor.Parser (parseProgram)
import Constructor.Path (Path (..), PathStep (..))
import Constructor.Sort (Sort (..))
import qualified GadtSketchSpec
import qualified HypTinfSpec
import qualified HypTwrSpec
import qualified LevelInferSpec
import qualified TinfSpec
import qualified TowerSpec
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
  putStrLn ""
  putStrLn "Tower scaffold:"
  towerOK <- mapM runInfer TowerSpec.tests
  putStrLn ""
  putStrLn "HypTwr (Tower carrier) parity:"
  hypTwrOK <- mapM runInfer HypTwrSpec.tests
  putStrLn ""
  putStrLn "GADT sketches:"
  gadtOK <- mapM runInfer GadtSketchSpec.tests
  if and (parseOK ++ inferOK ++ tinfOK ++ meetOK ++ hypTinfOK ++ towerOK ++ hypTwrOK ++ gadtOK) then exitSuccess else exitFailure
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
    , let boolP = Path [PsProgDecl 0]
      in Prog u
        [ DataDecl u boolP "Bool" [] (Star u 0)
            [ CtorDecl u "True"  (TyConRef u "Bool" boolP)
            , CtorDecl u "False" (TyConRef u "Bool" boolP)
            ]
        ]
    )
  , ( "Nat with arrow"
    , "data Nat : *0 { Z : Nat; S : Nat -> Nat }"
    , let natP = Path [PsProgDecl 0]
      in Prog u
        [ DataDecl u natP "Nat" [] (Star u 0)
            [ CtorDecl u "Z" (TyConRef u "Nat" natP)
            , CtorDecl u "S" (Arr u (TyConRef u "Nat" natP) (TyConRef u "Nat" natP))
            ]
        ]
    )
  , ( "nested data"
    , "data Type : *1 { Constr : Type; data Ty2 : Type { Foo : Ty2 } }"
    , let typeP = Path [PsProgDecl 0]
          ty2P  = Path [PsProgDecl 0, PsDeclIdx 1]
      in Prog u
        [ DataDecl u typeP "Type" [] (Star u 1)
            [ CtorDecl u "Constr" (TyConRef u "Type" typeP)
            , DataDecl u ty2P "Ty2" [] (TyConRef u "Type" typeP)
                [ CtorDecl u "Foo" (TyConRef u "Ty2" ty2P)
                ]
            ]
        ]
    )
  , ( "right-assoc arrow"
    , "data X : *0 { F : X -> X -> X }"
    , let xP = Path [PsProgDecl 0]
      in Prog u
        [ DataDecl u xP "X" [] (Star u 0)
            [ CtorDecl u "F" (Arr u (TyConRef u "X" xP)
                               (Arr u (TyConRef u "X" xP) (TyConRef u "X" xP)))
            ]
        ]
    )
  , ( "polymorphic universe — \8704l. *l"
    , "data Foo : \8704l. *l { c : Foo }"
    , let pBinder = Path [PsProgDecl 0, PsDataAnn]
          fooP    = Path [PsProgDecl 0]
      in Prog u
        [ DataDecl u fooP "Foo" []
            (ForallLv u "l" pBinder (StarVar u "l" pBinder 0))
            [ CtorDecl u "c" (TyConRef u "Foo" fooP)
            ]
        ]
    )
  , ( "polymorphic universe with offset — \8704l. *(l + 2)"
    , "data Bar : \8704l. *(l + 2) { d : Bar }"
    , let pBinder = Path [PsProgDecl 0, PsDataAnn]
          barP    = Path [PsProgDecl 0]
      in Prog u
        [ DataDecl u barP "Bar" []
            (ForallLv u "l" pBinder (StarVar u "l" pBinder 2))
            [ CtorDecl u "d" (TyConRef u "Bar" barP)
            ]
        ]
    )
  , ( "polymorphic universe — keyword 'forall'"
    , "data Q : forall l . *(l + 1) { q : Q }"
    , let pBinder = Path [PsProgDecl 0, PsDataAnn]
          qP      = Path [PsProgDecl 0]
      in Prog u
        [ DataDecl u qP "Q" []
            (ForallLv u "l" pBinder (StarVar u "l" pBinder 1))
            [ CtorDecl u "q" (TyConRef u "Q" qP)
            ]
        ]
    )
  , ( "parametric data — data List a : *0 { Nil : List a }"
    , "data List a : *0 { Nil : List a }"
    , let pa    = Path [PsProgDecl 0, PsDataParam 0]
          listP = Path [PsProgDecl 0]
          ap    = Path [PsProgDecl 0, PsDeclIdx 0, PsCtorTy, PsArrL]
      in Prog u
        [ DataDecl u listP "List" ["a"] (Star u 0)
            [ CtorDecl u "Nil"
                (App u ap (TyConRef u "List" listP) (TyParamRef u "a" pa))
            ]
        ]
    )
  , ( "parametric data with arrow ctor — data List a : *0 { Cons : a -> List a -> List a }"
    , "data List a : *0 { Cons : a -> List a -> List a }"
    , let pa     = Path [PsProgDecl 0, PsDataParam 0]
          listP  = Path [PsProgDecl 0]
          appL   = Path [PsProgDecl 0, PsDeclIdx 0, PsCtorTy, PsArrR, PsArrL]
          appR   = Path [PsProgDecl 0, PsDeclIdx 0, PsCtorTy, PsArrR, PsArrR, PsArrL]
      in Prog u
        [ DataDecl u listP "List" ["a"] (Star u 0)
            [ CtorDecl u "Cons"
                (Arr u (TyParamRef u "a" pa)
                  (Arr u (App u appL (TyConRef u "List" listP) (TyParamRef u "a" pa))
                          (App u appR (TyConRef u "List" listP) (TyParamRef u "a" pa))))
            ]
        ]
    )
  , ( "application — three-arg left-assoc f x y z = ((f x) y) z"
    , "data D : *0 { c : f x y z }"
    , let ap = Path [PsProgDecl 0, PsDeclIdx 0, PsCtorTy, PsArrL]
          dP = Path [PsProgDecl 0]
      in Prog u
        [ DataDecl u dP "D" [] (Star u 0)
            [ CtorDecl u "c"
                (App u ap
                  (App u ap
                    (App u ap (Var u "f") (Var u "x"))
                    (Var u "y"))
                  (Var u "z"))
            ]
        ]
    )
  ]
