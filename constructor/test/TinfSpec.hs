{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module TinfSpec (tests) where

import Constructor.Parser (parseProgram)
import Constructor.Tinf (TyErr (..), Tinf, TyResult (..), tinfProgram)
import Constructor.TyExpr (TyExpr (..))
import Data.Functor.Const (Const (..))
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Text.Megaparsec (errorBundlePretty)

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
    , expectOK "data List a : *0 { Nil : List a; Cons : a -> List a -> List a }"
        (Map.fromList [("List", 1)])
        (Map.fromList
          [ ("Nil", TyApp (TyCon "List") (TyVar "a"))
          , ("Cons", TyArr (TyVar "a")
                       (TyArr (TyApp (TyCon "List") (TyVar "a"))
                              (TyApp (TyCon "List") (TyVar "a"))))
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
    , expectOK "data Nat : *0 { Z : Nat }; data List a : *0 { Nil : List a }; data NatList : *0 { mk : List Nat }"
        (Map.fromList [("Nat", 0), ("List", 1), ("NatList", 0)])
        (Map.fromList
          [ ("Z",   TyCon "Nat")
          , ("Nil", TyApp (TyCon "List") (TyVar "a"))
          , ("mk",  TyApp (TyCon "List") (TyCon "Nat"))
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
