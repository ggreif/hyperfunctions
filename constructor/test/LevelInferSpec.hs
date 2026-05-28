{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module LevelInferSpec (tests) where

import Constructor.Level (Lv (..), starLevel)
import Constructor.LevelInfer (LevelMap, Lvl, LvErr (..), inferProgram)
import Constructor.Parser (parseProgram)
import Data.Functor.Const (Const (..))
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Text.Megaparsec (errorBundlePretty)

-- | Run the parser at the 'Lvl' carrier (with trivial @Const ()@
--   annotations), then read the inferred levels.
infer :: Text -> Either String LevelMap
infer src = case parseProgram @Lvl @(Const ()) "<test>" src of
  Left e  -> Left (errorBundlePretty e)
  Right p -> case inferProgram p of
    Left err -> Left (show err)
    Right lm -> Right lm

-- Build an Lv from a plain integer for readability in test expectations.
lv :: Int -> Lv
lv 0 = Z
lv n = S (lv (n - 1))

tests :: [(String, IO Bool)]
tests =
  [ ("Bool levels"
    , expectOK "data Bool : *0 { True : Bool; False : Bool }"
        [("Bool", lv 1), ("True", lv 0), ("False", lv 0)]
    )
  , ("Nat with arrow"
    , expectOK "data Nat : *0 { Z : Nat; S : Nat -> Nat }"
        [("Nat", lv 1), ("Z", lv 0), ("S", lv 0)]
    )
  , ("Nested data — Type/Constr/Ty2/Foo"
    , expectOK "data Type : *1 { Constr : Type; data Ty2 : Type { Foo : Ty2 } }"
        [("Type", lv 2), ("Constr", lv 1), ("Ty2", lv 1), ("Foo", lv 0)]
    )
  , ("*0 itself is at level 2"
    , do let want = starLevel 0
             got  = lv 2
         pass (want == got) "starLevel 0 should be (S (S Z)) = level 2"
    )
  , ("Heterogeneous arrow rejected — *0 -> *1"
    , expectErr "data X : *2 { F : *0 -> *1 }"
        (LevelTear (starLevel 0) (starLevel 1))
    )
  , ("Heterogeneous arrow via name — Nat -> *0"
    , expectErr "data Nat : *0 { Z : Nat }; data X : *0 { F : Nat -> *0 }"
        (LevelTear (lv 1) (starLevel 0))
    )
  , ("Unbound name"
    , expectErr "data X : *0 { F : NotDefined }"
        (Unbound "NotDefined")
    )
  , ("Duplicate name"
    , expectErr "data X : *0 { c : X }; data X : *0 { d : X }"
        (Duplicate "X")
    )
  , ("Two-universe coexistence (no cross-arrow)"
    , expectOK
        "data Type : *1 { TyBool : Type; TyNat : Type; TyFun : Type -> Type -> Type }; data Bool : *0 { True : Bool; False : Bool }"
        [ ("Type",   lv 2)
        , ("TyBool", lv 1), ("TyNat", lv 1), ("TyFun", lv 1)
        , ("Bool",   lv 1)
        , ("True",   lv 0), ("False", lv 0)
        ]
    )
  ]

expectOK :: Text -> [(Text, Lv)] -> IO Bool
expectOK src want = case infer src of
  Left e -> reportFail $ "expected OK but got error: " <> e
  Right got ->
    let wantMap = Map.fromList want
    in if got == wantMap
         then pure True
         else reportFail $
              "level map mismatch\n  want: " <> show wantMap <>
              "\n  got:  " <> show got

expectErr :: Text -> LvErr -> IO Bool
expectErr src wantErr = case infer src of
  Right lm -> reportFail $ "expected error " <> show wantErr <>
                           " but inference succeeded with " <> show lm
  Left e ->
    let wantStr = show wantErr
    in if wantStr == e
         then pure True
         else reportFail $
              "wrong error\n  want: " <> wantStr <>
              "\n  got:  " <> e

pass :: Bool -> String -> IO Bool
pass True  _   = pure True
pass False msg = reportFail msg

reportFail :: String -> IO Bool
reportFail msg = putStrLn ("    " <> msg) >> pure False
