{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

-- | Sketches of GADT-shaped tests, with what works today vs what is
--   blocked clearly marked.  The aim of this module is to lay out
--   /typical GADT examples/ as concrete programs and confirm — via
--   the actual elaborator — exactly which corners are reachable
--   without further grammar / typing work.
--
--   What we have:
--
--     * data declarations with type-expression annotations
--     * parametric data (@data T a : *0@)
--     * forward-only sibling references (later siblings see earlier
--       ones; not vice versa)
--     * self-referential kind annotations (@data Weird : Weird@
--       Tower-style stratification)
--     * tower-aware meet + kind coherence + occurs check
--
--   What we /don't/ have yet:
--
--     * GADT result-type refinement (each ctor's result must be the
--       parent applied to its params; no per-ctor specialisation)
--     * Type-level functions
--     * Mutual-recursion between siblings (forward references into
--       not-yet-declared sibling decls)
--     * Promotion of value-level ctors to types (DataKinds-style)
--     * Value-level expressions / pattern matching
--
--   The 'reachable' section below contains genuine end-to-end tests
--   that pass through 'parser → HypLinf → HypTwr'.  The 'blocked'
--   section contains 'expect-rejection' tests that confirm what the
--   error looks like today — they'll flip to 'expect-acceptance'
--   when the corresponding feature lands.
module GadtSketchSpec (tests) where

import Constructor.HypLinf (HypLinf, hypLinfRunWith)
import Constructor.HypTwr (HypTwr, HypTwrResult (..), hypTwrCtorTypes, hypTwrProgram)
import Constructor.LevelInfer (LvErr (..))
import Constructor.Parser (parseProgram)
import Data.Functor.Const (Const (..))
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Text.Megaparsec (errorBundlePretty)

tests :: [(String, IO Bool)]
tests =
  -- --- Reachable today -------------------------------------------
  [ accepts "GADT sketch: parametric Fin (no result refinement)"
      "data Nat : *0 { Z : Nat; S : Nat -> Nat };\
      \data Fin n : *0 { FZ : Fin n; FS : Fin n -> Fin n }"
      ["FZ", "FS", "Z", "S"]
  , accepts "GADT sketch: parametric Expr (typed-AST baseline)"
      "data Expr a : *0 { Lit : a -> Expr a; App : Expr a -> Expr a -> Expr a }"
      ["Lit", "App"]
  , accepts "GADT sketch: Iso flat (Weird-style; all ctors : Iso)"
      "data Iso : Iso { GetOne : Iso; GetTwo : Iso; GetThree : Iso }"
      ["GetOne", "GetTwo", "GetThree"]
  , accepts "GADT sketch: Weird end-to-end (TyConRef self-reference)"
      "data Weird : Weird { Level0 : Weird }"
      ["Level0"]

  -- --- Blocked by forward-mutual references ---------------------
  --
  -- The 'Iso singleton' family wants each ctor's type to be a
  -- DIFFERENT type, and those types either to be declared (Iso-sep)
  -- or to share their name with the ctor (Iso-cute).  Either way
  -- there are forward references between siblings — Iso's ctors
  -- reference One / Two / Three before they're declared, OR
  -- One / Two / Three reference Iso before it's declared.  The
  -- parser's binders today track only forward-only sibling
  -- visibility; the data binder is only added /after/ its decl is
  -- complete.  Mutual-reference support is its own feature.
  , rejectsAtLevel
      "GADT sketch: Iso singleton via separate type decls (BLOCKED: forward ref to Iso)"
      ("data One : Iso { OneCtor : One };\
       \data Two : Iso { TwoCtor : Two };\
       \data Three : Iso { ThreeCtor : Three };\
       \data Iso : Iso { GetOne : One; GetTwo : Two; GetThree : Three }")
      (Unbound "Iso")
  , rejectsAtLevel
      "GADT sketch: Iso cute singleton (BLOCKED: ctor name as type)"
      "data Iso : Iso { One : One; Two : Two; Three : Three }"
      (Unbound "One")
  , rejectsAtLevel
      "GADT sketch: Swap singleton (BLOCKED: mutual ctor-as-type reference)"
      "data Swap : Swap { Left : Right; Right : Left }"
      (Unbound "Right")

  -- --- Blocked by GADT result-type refinement --------------------
  --
  -- True 'Fin' has @FZ : Fin (S n)@ and @FS : Fin n -> Fin (S n)@,
  -- where each ctor's result type is the parent's tycon applied to
  -- a /specific/ index that may differ from other ctors.  Today
  -- ctorDecl just stores the parsed annotation verbatim — there's
  -- no machinery to enforce 'each ctor returns the parent tycon
  -- with the right number of arguments' nor to refine the index
  -- inside a pattern match arm.  When refinement-aware meet lands
  -- (the bind-direction guard via TyProc-meta identity, prepared
  -- by the TyView → TyProc lift in v0.1.0), these examples will
  -- start to make semantic sense.
  ]

-- | Helper: parse + elaborate end-to-end via HypLinf → HypTwr; assert
--   the extracted ctor map has exactly the expected keys.  Doesn't
--   pin types (the structural tests in HypTinfSpec / HypTwrSpec
--   already do that); just confirms the program reaches
--   materialisation with the right set of ctors.
accepts :: String -> Text -> [Text] -> (String, IO Bool)
accepts name src wantedCtors = (name, go)
  where
    go = case parseProgram @HypLinf @(Const ()) name src of
      Left e -> fail_ (errorBundlePretty e)
      Right pHypLinf -> case hypLinfRunWith @HypTwr pHypLinf of
        Left lv -> fail_ $ "level layer failed: " <> show lv
        Right (_, pTwr) -> case hypTwrProgram pTwr of
          Left ty -> fail_ $ "type layer failed: " <> show ty
          Right r -> case hypTwrCtorTypes r of
            Left e2 -> fail_ $ "materialize failed: " <> show e2
            Right m
              | Map.keysSet m == Map.keysSet (Map.fromList [(c, ()) | c <- wantedCtors])
                  -> pure True
              | otherwise -> fail_ $
                  "ctor keyset mismatch:\n  want: " <> show wantedCtors
                  <> "\n  got:  " <> show (Map.keys m)
            where _ = hypTwrDataTypes r

-- | Helper: parse OK + elaborate, expect a specific LvErr from the
--   level layer.  Documents that the program is REJECTED today and
--   pins the exact failure, so when the underlying gap is filled
--   (mutual-reference support, etc.) this test will trip and the
--   author will know to flip the marker.
rejectsAtLevel :: String -> Text -> LvErr -> (String, IO Bool)
rejectsAtLevel name src wantErr = (name, go)
  where
    go = case parseProgram @HypLinf @(Const ()) name src of
      Left e -> fail_ $ "parse error (test setup): " <> errorBundlePretty e
      Right pHypLinf -> case hypLinfRunWith @HypTwr pHypLinf of
        Left lv
          | lv == wantErr -> pure True
          | otherwise -> fail_ $
              "level error mismatch:\n  want: " <> show wantErr
              <> "\n  got:  " <> show lv
        Right _ -> fail_ $
          "expected level rejection (" <> show wantErr
          <> "), but program elaborated"

fail_ :: String -> IO Bool
fail_ msg = putStrLn ("    " <> msg) >> pure False
