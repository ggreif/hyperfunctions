{-# LANGUAGE OverloadedStrings #-}

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
module TowerSpec (tests) where

import Constructor.Level (Lv (..))
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
  ]

expectEq :: (Eq a, Show a) => a -> a -> IO Bool
expectEq got want
  | got == want = pure True
  | otherwise   = reportFail $
      "expected: " <> show want <> "\n  got:      " <> show got

reportFail :: String -> IO Bool
reportFail msg = putStrLn ("    " <> msg) >> pure False
