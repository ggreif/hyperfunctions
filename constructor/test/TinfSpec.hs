{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module TinfSpec (tests) where

import Constructor.Parser (parseProgram)
import Constructor.Path (Path (..), PathStep (..))
import Constructor.Tinf (TyErr (..), Tinf, TyResult (..), tinfProgram)
import Constructor.TyExpr (TyExpr (..))
import Data.Functor.Const (Const (..))
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Text.Megaparsec (errorBundlePretty)

-- | Path of the 0th type parameter of the @nth@ top-level declaration.
--   Mirrors the parser's @[PsProgDecl n, PsDataParam 0]@ for the
--   single-parameter cases under test.
param0Path :: Int -> Path
param0Path n = Path [PsProgDecl n, PsDataParam 0]

tests :: [(String, IO Bool)]
tests =
  [ ( "Tinf: empty program"
    , expectOK "" Map.empty Map.empty
    )
  , ( "Tinf: data Bool : *0 { True : Bool; False : Bool }"
    , expectOK "data Bool : *0 { True : Bool; False : Bool }"
        (Map.fromList [("Bool", 0)])
        (Map.fromList [("True", TyCon "Bool"), ("False", TyCon "Bool")])
    )
  , ( "Tinf: data Nat : *0 { Z : Nat; S : Nat -> Nat }"
    , expectOK "data Nat : *0 { Z : Nat; S : Nat -> Nat }"
        (Map.fromList [("Nat", 0)])
        (Map.fromList
          [ ("Z", TyCon "Nat")
          , ("S", TyArr (TyCon "Nat") (TyCon "Nat"))
          ])
    )
  , ( "Tinf: parametric data — data List a : *0 { Nil : List a; Cons : a -> List a -> List a }"
    , let pa = param0Path 0
      in expectOK "data List a : *0 { Nil : List a; Cons : a -> List a -> List a }"
           (Map.fromList [("List", 1)])
           (Map.fromList
             [ ("Nil", TyApp (TyCon "List") (TyVar "a" pa))
             , ("Cons", TyArr (TyVar "a" pa)
                          (TyArr (TyApp (TyCon "List") (TyVar "a" pa))
                                 (TyApp (TyCon "List") (TyVar "a" pa))))
             ])
    )
  , ( "Tinf: parameter goes out of scope after data body"
    , expectErr "data List a : *0 { Nil : List a }; data D : *0 { use : a }"
        (TyUnbound "a")
    )
  , ( "Tinf: unbound reference"
    , expectErr "data D : *0 { c : NotDefined }"
        (TyUnbound "NotDefined")
    )
  , ( "Tinf: duplicate data type"
    , expectErr "data Bool : *0 { T : Bool }; data Bool : *0 { F : Bool }"
        (TyDuplicateType "Bool")
    )
  , ( "Tinf: cross-decl reference — data NatList : *0 { mk : List Nat }"
    , let pa = param0Path 1  -- 'a' is param 0 of the 2nd top-level decl (List)
      in expectOK "data Nat : *0 { Z : Nat }; data List a : *0 { Nil : List a }; data NatList : *0 { mk : List Nat }"
           (Map.fromList [("Nat", 0), ("List", 1), ("NatList", 0)])
           (Map.fromList
             [ ("Z",   TyCon "Nat")
             , ("Nil", TyApp (TyCon "List") (TyVar "a" pa))
             , ("mk",  TyApp (TyCon "List") (TyCon "Nat"))
             ])
    )
  , ( "Tinf: distinct parameter paths — two 'a's are different vars (Stern-Gerlach)"
    , let pa1 = param0Path 0
          pa2 = param0Path 1
      in expectOK "data Box a : *0 { mk : a -> Box a }; data Bag a : *0 { mk2 : a -> Bag a }"
           (Map.fromList [("Box", 1), ("Bag", 1)])
           (Map.fromList
             [ ("mk",  TyArr (TyVar "a" pa1) (TyApp (TyCon "Box") (TyVar "a" pa1)))
             , ("mk2", TyArr (TyVar "a" pa2) (TyApp (TyCon "Bag") (TyVar "a" pa2)))
             ])
    )
  ]

expectOK :: Text -> Map.Map Text Int -> Map.Map Text TyExpr -> IO Bool
expectOK src wantDataTypes wantCtors =
  case parseProgram @Tinf @(Const ()) "<tinf>" src of
    Left e -> reportFail (errorBundlePretty e)
    Right p -> case tinfProgram p of
      Left err -> reportFail (show err)
      Right (TyResult dataTypes ctors)
        | dataTypes == wantDataTypes && ctors == wantCtors -> pure True
        | otherwise -> reportFail $
            "DataTypes\n  want: " <> show wantDataTypes <>
            "\n  got:  " <> show dataTypes <>
            "\nCtors\n  want: " <> show wantCtors <>
            "\n  got:  " <> show ctors

expectErr :: Text -> TyErr -> IO Bool
expectErr src wantErr = case parseProgram @Tinf @(Const ()) "<tinf-err>" src of
  Left e -> reportFail (errorBundlePretty e)
  Right p -> case tinfProgram p of
    Left err
      | err == wantErr -> pure True
      | otherwise -> reportFail $
          "expected error: " <> show wantErr <>
          "\n  got:           " <> show err
    Right r -> reportFail $ "expected error " <> show wantErr <>
                            " but got success: " <> show r

reportFail :: String -> IO Bool
reportFail msg = putStrLn ("    " <> msg) >> pure False
