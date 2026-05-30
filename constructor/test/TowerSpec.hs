{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

-- | Tower-arc scaffold tests.  Exercises:
--
--   * 'liftTower' / 'projectFirstRung' parity with 'procToTy'
--     (the invariant that justifies the lift)
--
--   * the vertical universe stream — each 'climb' advances one rung
--     in the 'Lv' ladder
--
--   * 'universeStream' as productive codata: the same stream viewed
--     at progressive climbs yields successive universes
--
--   * end-to-end on a multiply-nested @data@ program: parse through
--     'HypTinf', lift each ctor's 'TyProc' to a Tower, verify
--     first-rung parity against the materialised type
--
--   * Tower arc step 3 — tower-aware kind coherence.  An ill-kinded
--     mutant (@data Ty2 : *0@ nested inside @data Type : *1@) is
--     rejected at elaboration time with a 'TyMismatch' between
--     Ty2's annotation tower and the parent's TyConV-tower.
module TowerSpec (tests) where

import Constructor.HypLinf (HypLinf, hypLinfRunWith)
import Constructor.HypTinf
  ( HypTinf
  , HypTinfResult (..)
  , hypTinfCtorTypes
  , hypTinfProgram
  )
import Constructor.Level (Lv (..))
import Constructor.Parser (parseProgram)
import Constructor.Path (Path (..), PathStep (..))
import Constructor.Tinf (TyErr (..))
import Constructor.Tower
  ( climb
  , emptyKindEnv
  , horizontal
  , kindOf
  , liftTower
  , projectFirstRung
  , universeStream
  )
import Constructor.TyExpr (TyExpr (..))
import Constructor.TyProc (TyView (..), tyToProc, viewToTy)
import Data.Functor.Const (Const (..))
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Text.Megaparsec (errorBundlePretty)

tests :: [(String, IO Bool)]
tests =
  [ ( "Tower: projectFirstRung (liftTower _ p) ≡ procToTy p — nullary case"
    , let boolP = Path [PsProgDecl 0]
          ty    = TyCon "Bool" boolP
          tw    = liftTower emptyKindEnv (tyToProc ty)
      in expectEq (projectFirstRung tw) ty
    )
  , ( "Tower: projectFirstRung — compound case (List Nat)"
    , let listP = Path [PsProgDecl 0]
          natP  = Path [PsProgDecl 1]
          ty    = TyApp (TyCon "List" listP) (TyCon "Nat" natP)
          tw    = liftTower emptyKindEnv (tyToProc ty)
      in expectEq (projectFirstRung tw) ty
    )
  , ( "Tower: vertical stream above Bool — *0, *1, *2"
    , let boolP = Path [PsProgDecl 0]
          tw    = liftTower emptyKindEnv (tyToProc (TyCon "Bool" boolP))
          rung1 = viewToTy (horizontal (climb tw))
          rung2 = viewToTy (horizontal (climb (climb tw)))
          rung3 = viewToTy (horizontal (climb (climb (climb tw))))
      in do
        ok1 <- expectEq rung1 (TyUniv (S (S Z)))
        ok2 <- expectEq rung2 (TyUniv (S (S (S Z))))
        ok3 <- expectEq rung3 (TyUniv (S (S (S (S Z)))))
        pure (ok1 && ok2 && ok3)
    )
  , ( "Tower: universeStream Z — Z, S Z, S (S Z), …"
    , let s     = universeStream Z
          rung0 = viewToTy (horizontal s)
          rung1 = viewToTy (horizontal (climb s))
          rung2 = viewToTy (horizontal (climb (climb s)))
      in do
        ok0 <- expectEq rung0 (TyUniv Z)
        ok1 <- expectEq rung1 (TyUniv (S Z))
        ok2 <- expectEq rung2 (TyUniv (S (S Z)))
        pure (ok0 && ok1 && ok2)
    )
  , ( "Tower: vertical is the directed `:` arrow — climb walks codata"
    , -- Walk many rungs to confirm the stream is genuinely
      -- productive (no early termination, no laziness pitfall).
      let s = universeStream Z
          deepClimb 0 t = t
          deepClimb n t = deepClimb (n - 1 :: Int) (climb t)
          deep  = deepClimb 10 s
          want  = TyUniv (foldr (\_ acc -> S acc) Z [1..10 :: Int])
      in expectEq (viewToTy (horizontal deep)) want
    )

    -- --- End-to-end on parsed nested data --------------------------
  , ( "Tower: nested data (well-kinded) — parses, elaborates, lifts"
    , -- data Type : *1 { Constr : Type; data Ty2 : Type { Foo : Ty2 } }
      --
      -- Both inner members declare their inhabitation as @Type@, so
      -- the program is kind-coherent.  We verify two invariants:
      --   1. HypTinf accepts the program and materialises both ctors
      --      (Constr at Type, Foo at Ty2).
      --   2. For each ctor, lifting its meta-free TyProc to a Tower
      --      and projecting the first rung agrees with the
      --      materialised TyExpr.
      let typeP = Path [PsProgDecl 0]
          ty2P  = Path [PsProgDecl 0, PsDeclIdx 1]
          want  = Map.fromList
                    [ ("Constr", TyCon "Type" typeP)
                    , ("Foo",    TyCon "Ty2"  ty2P)
                    ]
      in withHypTinf
           "data Type : *1 { Constr : Type; data Ty2 : Type { Foo : Ty2 } }"
           $ \r -> case hypTinfCtorTypes r of
             Left err -> reportFail $ "materialize failed: " <> show err
             Right materialised -> do
               ok1 <- expectEq materialised want
               -- Tower lift parity: ctors are non-parametric (no
               -- metas), so projectFirstRung agrees with materialize.
               -- liftTower now consumes the kind env produced by
               -- HypTinf's elaboration of each data's kind annotation.
               let procs = hypTinfCtors r
                   env_  = hypTinfKindEnv r
                   towers = Map.map (liftTower env_) procs
                   projected = Map.map projectFirstRung towers
               ok2 <- expectEq projected want
               pure (ok1 && ok2)
    )
  , ( "Tower: nested data (ill-kinded mutant — rejected by step 3)"
    , -- data Type : *1 { Constr : Type; data Ty2 : *0 { Foo : Ty2 } }
      --
      -- Ty2 declares its kind as *0 rather than Type.  Both Constr
      -- and Ty2 still sit at level 1 inside Type's body, so the
      -- level layer is happy.  But Ty2 has "snuck out" of Type's
      -- kind-namespace: it inhabits *0, not Type.  This is the
      -- textbook kind mismatch that level inference cannot see.
      --
      -- Tower arc step 3 introduced tower-aware kind coherence in
      -- 'HypTinf.dataDecl': a nested data's annotation tower must
      -- agree coinductively with the parent's TyConV-tower.  Here
      -- Ty2's tower starts at @TyUnivV *0@ while the parent's starts
      -- at @TyConV "Type"@ — sameView returns False at rung 0, so
      -- elaboration fails with TyMismatch.
      let typeP = Path [PsProgDecl 0]
      in expectKindMismatch
           "data Type : *1 { Constr : Type; data Ty2 : *0 { Foo : Ty2 } }"
           (TyUniv (S (S Z))) (TyCon "Type" typeP)
    )

    -- --- Step-2 kindOf coalgebra ----------------------------------
  , ( "kindOf: TyUnivV lv steps to TyUnivV (S lv)"
    , let k0 = kindOf emptyKindEnv (TyUnivV Z)
          k1 = kindOf emptyKindEnv (TyUnivV (S Z))
      in do
        ok0 <- expectEq (viewToTy k0) (TyUniv (S Z))
        ok1 <- expectEq (viewToTy k1) (TyUniv (S (S Z)))
        pure (ok0 && ok1)
    )
  , ( "kindOf: TyConV in env returns its declared kind annotation"
    , -- For data Type : *1 { … }, kindOf (TyConV \"Type\" typeP)
      -- under the elaborated env should give TyUnivV (Lv of *1) = *1
      -- (i.e. S(S(S Z))).  We exercise via end-to-end HypTinf.
      withHypTinf
        "data Type : *1 { Constr : Type }"
        $ \r ->
          let typeP = Path [PsProgDecl 0]
              k     = kindOf (hypTinfKindEnv r) (TyConV "Type" typeP)
          in expectEq (viewToTy k) (TyUniv (S (S (S Z))))
    )
  , ( "kindOf: well-kinded Ty2's rung 1 is TyConV \"Type\""
    , -- The property step 3 exploits: under a well-kinded program,
      -- kindOf walks one rung up to TyConV "Type" (the parent's
      -- name), and from there to *1 — which then agrees with the
      -- parent's TyConV-tower coinductively.  The ill-kinded mutant
      -- is now caught earlier by 'HypTinf.dataDecl' (see the
      -- preceding test); here we just record the well-kinded shape.
      withHypTinf
        "data Type : *1 { Constr : Type; data Ty2 : Type { Foo : Ty2 } }"
        $ \r ->
          let ty2P = Path [PsProgDecl 0, PsDeclIdx 1]
              k    = kindOf (hypTinfKindEnv r) (TyConV "Ty2" ty2P)
          in expectEq (viewToTy k) (TyCon "Type" (Path [PsProgDecl 0]))
    )
  ]

-- | Pipeline: parser → 'HypLinf' (level inference, producing a
--   polymorphic LvAnnot-decorated term) → 'HypTinf' (type
--   inference, fed by the LvAnnot input) → 'HypTinfResult'.
--
--   This sequencing replaces the older parallel architecture
--   (each carrier consumed the parser directly) with a typed
--   dependency: 'HypTinf' now receives level-annotated input from
--   'HypLinf' via the impredicative third slot of 'runHypLinf'.
withHypTinf :: Text -> (HypTinfResult -> IO Bool) -> IO Bool
withHypTinf src k = case parseProgram @HypLinf @(Const ()) "<tower>" src of
  Left e  -> reportFail $ "parse error: " <> errorBundlePretty e
  Right p -> case hypLinfRunWith @HypTinf p of
    Left lvErr -> reportFail $ "level inference error: " <> show lvErr
    Right (_, pTinf) -> case hypTinfProgram pTinf of
      Left err -> reportFail $ "type inference error: " <> show err
      Right r  -> k r

expectEq :: (Eq a, Show a) => a -> a -> IO Bool
expectEq got want
  | got == want = pure True
  | otherwise   = reportFail $
      "expected: " <> show want <> "\n  got:      " <> show got

-- | Run a source program through 'HypTinf' and expect a 'TyMismatch'
--   carrying the given (member, parent) views materialised to TyExpr.
--   Used to assert that tower-aware kind coherence (Tower arc step 3)
--   rejects an ill-kinded mutant with the right shape.
expectKindMismatch :: Text -> TyExpr -> TyExpr -> IO Bool
expectKindMismatch src wantMember wantParent =
  case parseProgram @HypLinf @(Const ()) "<tower-mismatch>" src of
    Left e -> reportFail $ "parse error: " <> errorBundlePretty e
    Right p -> case hypLinfRunWith @HypTinf p of
      Left lvErr -> reportFail $ "level inference error: " <> show lvErr
      Right (_, pTinf) -> case hypTinfProgram pTinf of
        Left (TyMismatch m k)
          | m == wantMember && k == wantParent -> pure True
          | otherwise -> reportFail $
              "expected TyMismatch " <> show wantMember <> " " <> show wantParent
              <> "\n  got: TyMismatch " <> show m <> " " <> show k
        Left err -> reportFail $ "expected TyMismatch, got: " <> show err
        Right _  -> reportFail "expected elaboration failure, but it succeeded"

reportFail :: String -> IO Bool
reportFail msg = putStrLn ("    " <> msg) >> pure False
