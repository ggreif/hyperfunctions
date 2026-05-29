{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

-- | B-side type-inference parity tests.  For each surface program,
--   parse it twice — once through 'Tinf' (A-side, the syntactic
--   baseline), once through 'HypTinf' (B-side, the hyperfunction
--   web) — and verify the two agree after extracting 'HypTinf's
--   processes back to syntax via 'procToTy'.
--
--   These tests carry no expected literals of their own; they reuse
--   the A-side's expectations as oracle.  When A's tests pass and
--   B's parity tests pass, the two carriers agree pointwise on the
--   current corpus — modulo extraction, which is what we want at
--   commit-4 scope (the web has no expressive power over the tree
--   yet; the algebraic structure becomes visible only once
--   commit-5's unifier rewires processes).
module HypTinfSpec (tests) where

import Constructor.HypTinf
  ( HypTinf
  , HypTinfResult (..)
  , hypTinfCtorTypes
  , hypTinfProgram
  )
import Constructor.Parser (parseProgram)
import Constructor.Tinf (Tinf, TyResult (..), tinfProgram)
import Data.Functor.Const (Const (..))
import Data.Text (Text)
import Text.Megaparsec (errorBundlePretty)

tests :: [(String, IO Bool)]
tests =
  [ parity "HypTinf parity: empty program" ""
  , parity "HypTinf parity: data Bool"
      "data Bool : *0 { True : Bool; False : Bool }"
  , parity "HypTinf parity: data Nat"
      "data Nat : *0 { Z : Nat; S : Nat -> Nat }"
  , parity "HypTinf parity: parametric data — List a"
      "data List a : *0 { Nil : List a; Cons : a -> List a -> List a }"
  , parity "HypTinf parity: cross-decl — List Nat"
      "data Nat : *0 { Z : Nat }; data List a : *0 { Nil : List a }; data NatList : *0 { mk : List Nat }"
  , parity "HypTinf parity: Stern-Gerlach (Box a / Bag a)"
      "data Box a : *0 { mk : a -> Box a }; data Bag a : *0 { mk2 : a -> Bag a }"
  ]

-- | Run the same source through both carriers and check the extracted
--   results agree.  Each test owns one program; the oracle is A's
--   answer, not a hand-written expectation.
parity :: String -> Text -> (String, IO Bool)
parity name src = (name, go)
  where
    go = case parseProgram @Tinf @(Const ()) name src of
      Left e -> reportFail (errorBundlePretty e)
      Right pA -> case parseProgram @HypTinf @(Const ()) name src of
        Left e -> reportFail (errorBundlePretty e)
        Right pB -> case (tinfProgram pA, hypTinfProgram pB) of
          (Left ea, Left eb)
            | ea == eb  -> pure True
            | otherwise -> reportFail $
                "errors disagree:\n  A: " <> show ea <> "\n  B: " <> show eb
          (Left ea, Right _) -> reportFail $
            "A errored but B succeeded; A error: " <> show ea
          (Right _, Left eb) -> reportFail $
            "B errored but A succeeded; B error: " <> show eb
          (Right rA, Right rB) ->
            let dataA = tyResultDataTypes rA
                ctorA = tyResultCtors rA
                dataB = hypTinfDataTypes rB
            in case hypTinfCtorTypes rB of
              Left err -> reportFail $
                "B failed to materialize ctor types: " <> show err
              Right ctorB
                | dataA == dataB && ctorA == ctorB -> pure True
                | otherwise -> reportFail $
                    "results disagree:\n" <>
                    "  A dataTypes: " <> show dataA <> "\n" <>
                    "  B dataTypes: " <> show dataB <> "\n" <>
                    "  A ctors:     " <> show ctorA <> "\n" <>
                    "  B ctors:     " <> show ctorB

reportFail :: String -> IO Bool
reportFail msg = putStrLn ("    " <> msg) >> pure False
