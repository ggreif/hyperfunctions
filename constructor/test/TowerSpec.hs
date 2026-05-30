{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

-- | Tower-arc commit-1 scaffold tests.  Exercises:
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
--   * an ill-kinded mutant (Ty2 declared with kind @*0@ inside @Type@'s
--     body): currently accepted because the kind-coherence check is
--     not yet implemented.  This test is a regression witness for the
--     Tower arc step 3 — when tower-aware 'meet' lands, the mutant
--     will start being rejected with a kind-mismatch; flip the
--     'expectAccept' to 'expectKindMismatch' then.
module TowerSpec (tests) where

import Constructor.HypTinf
  ( HypTinf
  , HypTinfResult (..)
  , hypTinfCtorTypes
  , hypTinfProgram
  )
import Constructor.Level (Lv (..))
import Constructor.Parser (parseProgram)
import Constructor.Path (Path (..), PathStep (..))
import Constructor.Tower
  ( climb
  , horizontal
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
          tw    = liftTower (S Z) (tyToProc ty)
      in expectEq (projectFirstRung tw) ty
    )
  , ( "Tower: projectFirstRung — compound case (List Nat)"
    , let listP = Path [PsProgDecl 0]
          natP  = Path [PsProgDecl 1]
          ty    = TyApp (TyCon "List" listP) (TyCon "Nat" natP)
          tw    = liftTower (S Z) (tyToProc ty)
      in expectEq (projectFirstRung tw) ty
    )
  , ( "Tower: vertical stream above Bool — *0, *1, *2"
    , let boolP = Path [PsProgDecl 0]
          tw    = liftTower (S Z) (tyToProc (TyCon "Bool" boolP))
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
               let procs = hypTinfCtors r
                   towers = Map.map (liftTower (S (S Z))) procs
                   projected = Map.map projectFirstRung towers
               ok2 <- expectEq projected want
               pure (ok1 && ok2)
    )
  , ( "Tower: nested data (ill-kinded mutant — currently accepted)"
    , -- data Type : *1 { Constr : Type; data Ty2 : *0 { Foo : Ty2 } }
      --
      -- Ty2 declares its kind as *0 rather than Type.  Both Constr
      -- and Ty2 still sit at level 1 inside Type's body, so the
      -- level layer is happy.  But Ty2 has "snuck out" of Type's
      -- kind-namespace: it inhabits *0, not Type.  This is the
      -- textbook kind mismatch that level inference cannot see.
      --
      -- Today HypTinf accepts the program (no kind coherence check
      -- is implemented).  Tower arc step 3 will introduce tower-aware
      -- `meet` with directed vertical unification, at which point
      -- this mutant will be rejected with a kind mismatch.
      --
      -- @TODO(tower-arc-step-3): flip this from 'expectAccept' to
      -- 'expectKindMismatch' once tower-aware meet lands.
      withHypTinf
        "data Type : *1 { Constr : Type; data Ty2 : *0 { Foo : Ty2 } }"
        $ \_r -> pure True
    )
  ]

-- | Parse a source program through the 'HypTinf' carrier and pass
--   the resulting 'HypTinfResult' to a continuation.  Reports parse
--   or elaboration failures as test failures.
withHypTinf :: Text -> (HypTinfResult -> IO Bool) -> IO Bool
withHypTinf src k = case parseProgram @HypTinf @(Const ()) "<tower>" src of
  Left e -> reportFail $ "parse error: " <> errorBundlePretty e
  Right p -> case hypTinfProgram p of
    Left err -> reportFail $ "elaboration error: " <> show err
    Right r  -> k r

expectEq :: (Eq a, Show a) => a -> a -> IO Bool
expectEq got want
  | got == want = pure True
  | otherwise   = reportFail $
      "expected: " <> show want <> "\n  got:      " <> show got

reportFail :: String -> IO Bool
reportFail msg = putStrLn ("    " <> msg) >> pure False
