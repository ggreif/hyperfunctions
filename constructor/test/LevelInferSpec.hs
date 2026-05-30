{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module LevelInferSpec (tests) where

import Constructor.AST (Tree (..))
import Constructor.HfLvl (HfLvl, inferProgramHf)
import Constructor.HypLinf (HypLinf, hypLinfProgram, solveLevelsHypLinf)
import Constructor.Level (Lv (..), starLevel)
import Constructor.LevelInfer (LevelMap, Lvl, LvErr (..), inferProgram)
import Constructor.Parser (parseProgram)
import Constructor.Path (Path (..), PathStep (..))
import Constructor.Tc (LvAnnot (..), Tc, solveLevels, tcProgram, tcRunWith)
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
  , ("Hyper carrier parity — Lvl == HfLvl on Nat"
    , parityLvlHf "data Nat : *0 { Z : Nat; S : Nat -> Nat }"
        [("Nat", lv 1), ("Z", lv 0), ("S", lv 0)]
    )
  , ("Tc carrier parity — Lvl == Tc + solveLevels on Nat"
    , parityLvlTc "data Nat : *0 { Z : Nat; S : Nat -> Nat }"
        [("Nat", lv 1), ("Z", lv 0), ("S", lv 0)]
    )
  , ("tcRunWith @Tree — polymorphic LvAnnot-decorated term"
    , tcRunWithTreeCheck
    )
  , ("Architecture B parity — HypLinf + solveLevelsHypLinf on Nat"
    , parityLvlHypLinf "data Nat : *0 { Z : Nat; S : Nat -> Nat }"
        [("Nat", lv 1), ("Z", lv 0), ("S", lv 0)]
    )
  , ("Architecture B parity — HypLinf on nested data"
    , parityLvlHypLinf "data Type : *1 { Constr : Type; data Ty2 : Type { Foo : Ty2 } }"
        [("Type", lv 2), ("Constr", lv 1), ("Ty2", lv 1), ("Foo", lv 0)]
    )
  , ("Architecture B parity — HypLinf on heterogeneous arrow rejects"
    , parityRejectHypLinf "data X : *2 { F : *0 -> *1 }"
    )
  , ("Polymorphic — data Foo : \8704l. *(l + 2) { c : Foo } (A side)"
    , let p = Path [PsProgDecl 0, PsDataAnn]
      in polyDataLvl "data Foo : \8704l. *(l + 2) { c : Foo }"
           [("Foo", S (LVar p)), ("c", LVar p)]
    )
  , ("Polymorphic with arrow — data Foo : \8704l. *(l + 2) { c : Foo -> Foo } (A side)"
    , let p = Path [PsProgDecl 0, PsDataAnn]
      in polyDataLvl "data Foo : \8704l. *(l + 2) { c : Foo -> Foo }"
           [("Foo", S (LVar p)), ("c", LVar p)]
    )
  , ("Polymorphic — A vs B parity on \8704l. *(l + 2)"
    , parityPolyAB "data Foo : \8704l. *(l + 2) { c : Foo -> Foo }"
    )
  , ("HypLinf — data Weird : Weird (stratified self-typing)"
    , -- B-side-only (A's 'Lvl' / 'Tc' have no fixpoint at 'predLv
      -- (LVar _)' and would reject).  HypLinf accepts via:
      --   * pre-bind of @n@ to @hPure (LVar declPath)@ before
      --     elaborating the kind annotation (so the inner
      --     'tyConRef "Weird"' looks up something rather than
      --     failing 'Unbound');
      --   * 'predLv (LVar p) = Just (LVar p)' — the level
      --     coordinate's fixpoint at parametric levels.
      -- Expected level map: both Weird and Level0 at LVar
      -- weirdPath (the data and its sole ctor are at the same
      -- parametric level; the offset distinguishing them lives in
      -- 'TyConV's deck-shift slot in the Tower, not in 'Lv').
      let weirdP = Path [PsProgDecl 0]
          src    = "data Weird : Weird { Level0 : Weird }"
          want   = Map.fromList
                     [ ("Weird",  LVar weirdP)
                     , ("Level0", LVar weirdP)
                     ]
          got = case parseProgram @HypLinf @(Const ()) "<weird>" src of
            Left e  -> Left (errorBundlePretty e)
            Right p -> either (Left . show) Right
                              (hypLinfProgram p >>= solveLevelsHypLinf)
      in case got of
        Right lm | lm == want -> pure True
        Right lm -> reportFail $
          "Weird level map mismatch:\n  want: " <> show want <>
          "\n  got:  " <> show lm
        Left e -> reportFail $
          "expected HypLinf to accept Weird : Weird, got error: " <> e
    )
  ]

-- | Run the same source through both the classical 'Lvl' carrier and the
--   hyperfunction-backed 'HfLvl' carrier, then check that both agree with
--   the expected level map.  One regression suffices as a warm-up — the
--   hyperfunction encoding adds no power for flat levels, so the result
--   *must* be identical bit-for-bit.
parityLvlHf :: Text -> [(Text, Lv)] -> IO Bool
parityLvlHf src want = do
  let wantMap = Map.fromList want
      lvlR = case parseProgram @Lvl @(Const ()) "<parity>" src of
        Left e  -> Left (errorBundlePretty e)
        Right p -> either (Left . show) Right (inferProgram p)
      hfR = case parseProgram @HfLvl @(Const ()) "<parity>" src of
        Left e  -> Left (errorBundlePretty e)
        Right p -> either (Left . show) Right (inferProgramHf p)
  case (lvlR, hfR) of
    (Right a, Right b) | a == b && a == wantMap -> pure True
    _ -> reportFail $
           "Lvl:  " <> show lvlR <> "\n    " <>
           "HfLvl: " <> show hfR  <> "\n    " <>
           "want:  " <> show wantMap

-- | Run the same source through 'Lvl' and through 'Tc' + 'solveLevels';
--   both must produce the same 'LevelMap'.  The point is to confirm the
--   constraint-gathering carrier's AST-preserving output, when projected
--   back to a level map, agrees with the direct streaming pass.
parityLvlTc :: Text -> [(Text, Lv)] -> IO Bool
parityLvlTc src want = do
  let wantMap = Map.fromList want
      lvlR = case parseProgram @Lvl @(Const ()) "<parity>" src of
        Left e  -> Left (errorBundlePretty e)
        Right p -> either (Left . show) Right (inferProgram p)
      tcR = case parseProgram @Tc @(Const ()) "<parity>" src of
        Left e  -> Left (errorBundlePretty e)
        Right p -> either (Left . show) Right (tcProgram p >>= solveLevels)
  case (lvlR, tcR) of
    (Right a, Right b) | a == b && a == wantMap -> pure True
    _ -> reportFail $
           "Lvl: " <> show lvlR <> "\n    " <>
           "Tc:  " <> show tcR  <> "\n    " <>
           "want: " <> show wantMap

-- | Architecture B parity: 'HypLinf' (hyperfunction web) must agree
--   with 'Lvl' (sheet-driven) on v0 inputs — the architectures are
--   semantically identical for flat-level inference.
parityLvlHypLinf :: Text -> [(Text, Lv)] -> IO Bool
parityLvlHypLinf src want = do
  let wantMap = Map.fromList want
      lvlR = case parseProgram @Lvl @(Const ()) "<parity>" src of
        Left e  -> Left (errorBundlePretty e)
        Right p -> either (Left . show) Right (inferProgram p)
      hypR = case parseProgram @HypLinf @(Const ()) "<parity>" src of
        Left e  -> Left (errorBundlePretty e)
        Right p -> either (Left . show) Right (hypLinfProgram p >>= solveLevelsHypLinf)
  case (lvlR, hypR) of
    (Right a, Right b) | a == b && a == wantMap -> pure True
    _ -> reportFail $
           "Lvl:     " <> show lvlR <> "\n    " <>
           "HypLinf: " <> show hypR <> "\n    " <>
           "want:    " <> show wantMap

-- | 'HypLinf' must reject the same heterogeneous-arrow cases that
--   'Lvl' rejects.  Both should produce a 'LevelTear' error.
parityRejectHypLinf :: Text -> IO Bool
parityRejectHypLinf src = do
  let lvlR = case parseProgram @Lvl @(Const ()) "<reject>" src of
        Left e  -> Left (errorBundlePretty e)
        Right p -> either (Left . show) Right (inferProgram p)
      hypR = case parseProgram @HypLinf @(Const ()) "<reject>" src of
        Left e  -> Left (errorBundlePretty e)
        Right p -> either (Left . show) Right (hypLinfProgram p >>= solveLevelsHypLinf)
  case (lvlR, hypR) of
    (Left _, Left _) -> pure True   -- both rejected; agree
    _ -> reportFail $
           "Lvl:     " <> show lvlR <> "\n    " <>
           "HypLinf: " <> show hypR <> "\n    (both should reject)"

-- | Polymorphic-data parity for the A side: parse a polymorphic source
--   via 'Lvl', verify the produced 'LevelMap' contains the expected
--   level expressions (including 'LVar' references for unresolved
--   polymorphic levels).
polyDataLvl :: Text -> [(Text, Lv)] -> IO Bool
polyDataLvl src want = do
  let wantMap = Map.fromList want
  case parseProgram @Lvl @(Const ()) "<poly>" src of
    Left e  -> reportFail (errorBundlePretty e)
    Right p -> case inferProgram p of
      Left err -> reportFail (show err)
      Right got
        | got == wantMap -> pure True
        | otherwise -> reportFail $
            "level map mismatch\n  want: " <> show wantMap <>
            "\n  got:  " <> show got

-- | A vs B parity on a polymorphic source: 'Lvl' and 'HfLvl' must
--   produce identical 'LevelMap's, including the 'LVar' references.
parityPolyAB :: Text -> IO Bool
parityPolyAB src = do
  let lvlR = case parseProgram @Lvl @(Const ()) "<parity-poly>" src of
        Left e  -> Left (errorBundlePretty e)
        Right p -> either (Left . show) Right (inferProgram p)
      hfR = case parseProgram @HfLvl @(Const ()) "<parity-poly>" src of
        Left e  -> Left (errorBundlePretty e)
        Right p -> either (Left . show) Right (inferProgramHf p)
  case (lvlR, hfR) of
    (Right a, Right b) | a == b -> pure True
    _ -> reportFail $
           "Lvl:   " <> show lvlR <> "\n    " <>
           "HfLvl: " <> show hfR

-- | Demonstrate 'tcRunWith' producing a 'Tree' decorated with 'LvAnnot'.
--   Pattern-matches the resulting Tree against the expected structure +
--   level annotations.  Confirms the polymorphic term slot is genuinely
--   re-interpretable at any 'Lang' carrier (here, 'Tree').
tcRunWithTreeCheck :: IO Bool
tcRunWithTreeCheck = do
  let src = "data X : *0 { c : X }"
  case parseProgram @Tc @(Const ()) "<tree-annot>" src of
    Left e -> reportFail (errorBundlePretty e)
    Right p -> case tcRunWith @Tree p of
      Left err -> reportFail (show err)
      Right (_, tree)
        | Prog LvAProg
            [ DataDecl (LvADecl lnX) _ "X" []
                (Star (LvAExpr lvStar) 0)
                [ CtorDecl (LvADecl lcC) "c" (Var (LvAExpr lvVar) "X")
                ]
            ] <- tree
        , lnX    == lv 1  -- X at level 1 (data inhabiting *0)
        , lvStar == lv 2  -- *0 itself at level 2
        , lcC    == lv 0  -- c at level 0 (value of X)
        , lvVar  == lv 1  -- the 'X' reference, at level 1 (same as X)
        -> pure True
      Right (_, tree) -> reportFail $ "unexpected tree shape:\n    " <> show tree

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
