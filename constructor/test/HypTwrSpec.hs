{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

-- | Step-4 carrier ('Constructor.HypTwr') parity tests.  Each program
--   is run through both B-side type-inference paths:
--
--     parser → HypLinf → HypTinf  (TyProc carrier; existing)
--     parser → HypLinf → HypTwr   (Tower   carrier; new)
--
--   and the extracted ctor-type maps must agree.  The Tower carrier
--   emits each elaborated type as a first-class up-tower; for
--   metavariable-free corpora — which is everything we have today —
--   projecting the first rung back to 'TyExpr' must reproduce
--   'HypTinf.hypTinfCtorTypes' exactly.
--
--   Tests in this module witness that step-4's representation change
--   is observationally a no-op at the horizontal layer; the
--   tower-specific wins (Weird-style stratification, directed-meet
--   along the vertical) land in subsequent commits.
module HypTwrSpec (tests) where

import Constructor.HypLinf (HypLinf, hypLinfRunWith)
import Constructor.HypTinf (HypTinf, HypTinfResult (..), hypTinfCtorTypes, hypTinfProgram)
import Constructor.HypTwr (HypTwr, HypTwrResult (..), hypTwrCtorTypes, hypTwrProgram)
import Constructor.Parser (parseProgram)
import Data.Functor.Const (Const (..))
import Data.Text (Text)
import Text.Megaparsec (errorBundlePretty)

tests :: [(String, IO Bool)]
tests =
  [ parity "HypTwr parity: empty program" ""
  , parity "HypTwr parity: data Bool"
      "data Bool : *0 { True : Bool; False : Bool }"
  , parity "HypTwr parity: data Nat"
      "data Nat : *0 { Z : Nat; S : Nat -> Nat }"
  , parity "HypTwr parity: parametric data — List a"
      "data List a : *0 { Nil : List a; Cons : a -> List a -> List a }"
  , parity "HypTwr parity: cross-decl — List Nat"
      "data Nat : *0 { Z : Nat }; data List a : *0 { Nil : List a }; data NatList : *0 { mk : List Nat }"
  , parity "HypTwr parity: nested data — Type/Constr/Ty2/Foo"
      "data Type : *1 { Constr : Type; data Ty2 : Type { Foo : Ty2 } }"
    -- End-to-end @data Weird : Weird@ through the full pipeline:
    -- parser → HypLinf (with pre-bind for self-reference and the
    -- 'predLv (LVar p) = Just (LVar p)' fixpoint) → HypTinf /
    -- HypTwr.  Both type-inference carriers must accept and produce
    -- @Level0 : Weird@ as the extracted ctor; both must agree.
    -- This is the test that demonstrates the level-layer +
    -- Tower-layer accommodations close the loop end-to-end.
  , parity "HypTwr parity: data Weird : Weird (stratified self-typing)"
      "data Weird : Weird { Level0 : Weird }"
  ]

-- | Run the same source through HypTinf and HypTwr (both behind
--   HypLinf) and check the extracted ctor-type maps agree.
parity :: String -> Text -> (String, IO Bool)
parity name src = (name, go)
  where
    go = case parseProgram @HypLinf @(Const ()) name src of
      Left e -> reportFail (errorBundlePretty e)
      Right pHypLinf -> case (runHypTinf pHypLinf, runHypTwr pHypLinf) of
        (Left lvA, Left lvB)
          | lvA == lvB -> pure True
          | otherwise -> reportFail $
              "level errors disagree:\n  HypTinf path: " <> show lvA
              <> "\n  HypTwr path:  " <> show lvB
        (Left lvA, Right _) -> reportFail $
          "HypTinf path level-errored but HypTwr path succeeded: " <> show lvA
        (Right _, Left lvB) -> reportFail $
          "HypTwr path level-errored but HypTinf path succeeded: " <> show lvB
        (Right rA, Right rB) -> case (rA, rB) of
          (Left ea, Left eb)
            | ea == eb  -> pure True
            | otherwise -> reportFail $
                "type errors disagree:\n  HypTinf: " <> show ea
                <> "\n  HypTwr:  " <> show eb
          (Left ea, Right _) -> reportFail $
            "HypTinf errored but HypTwr succeeded: " <> show ea
          (Right _, Left eb) -> reportFail $
            "HypTwr errored but HypTinf succeeded: " <> show eb
          (Right (ctA, dataA), Right (ctB, dataB))
            | ctA == ctB && dataA == dataB -> pure True
            | otherwise -> reportFail $
                "results disagree:\n" <>
                "  HypTinf dataTypes: " <> show dataA <> "\n" <>
                "  HypTwr  dataTypes: " <> show dataB <> "\n" <>
                "  HypTinf ctors:     " <> show ctA <> "\n" <>
                "  HypTwr  ctors:     " <> show ctB

    runHypTinf pHypLinf = case hypLinfRunWith @HypTinf pHypLinf of
      Left lv -> Left lv
      Right (_, pTinf) -> Right $ case hypTinfProgram pTinf of
        Left err -> Left err
        Right r  -> case hypTinfCtorTypes r of
          Left err -> Left err
          Right ct -> Right (ct, fst3 r)
      where
        fst3 r = let dt = hypTinfDataTypes r in dt

    runHypTwr pHypLinf = case hypLinfRunWith @HypTwr pHypLinf of
      Left lv -> Left lv
      Right (_, pTwr) -> Right $ case hypTwrProgram pTwr of
        Left err -> Left err
        Right r  -> case hypTwrCtorTypes r of
          Left err -> Left err
          Right ct -> Right (ct, fst3 r)
      where
        fst3 r = let dt = hypTwrDataTypes r in dt

reportFail :: String -> IO Bool
reportFail msg = putStrLn ("    " <> msg) >> pure False
