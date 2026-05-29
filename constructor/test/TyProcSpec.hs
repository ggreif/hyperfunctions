{-# LANGUAGE OverloadedStrings #-}

-- | Direct tests for 'Constructor.TyProc.meet'.
--
--   Unlike 'TinfSpec' / 'HypTinfSpec', these exercise the algebra
--   without going through a 'Lang' carrier or the parser — `meet` is
--   built as commit-5 *apparatus* without a carrier-level customer
--   yet, so the tests build 'TyProc's directly from 'TyExpr's via
--   'tyToProc' and call `meet` pointwise.
module TyProcSpec (tests) where

import Constructor.Path (Path (..), PathStep (..))
import Constructor.Tinf (TyErr (..))
import Constructor.TyExpr (TyExpr (..))
import Constructor.TyProc (meet, procToTy, tyToProc)

tests :: [(String, IO Bool)]
tests =
  [ ( "meet: TyCon ≡ TyCon (same)"
    , expectOK
        (TyCon "Nat")
        (TyCon "Nat")
        (TyCon "Nat")
    )
  , ( "meet: TyCon ≢ TyCon (different)"
    , expectMismatch
        (TyCon "Nat")
        (TyCon "Bool")
    )
  , ( "meet: TyArr ≡ TyArr — congruent children"
    , expectOK
        (TyArr (TyCon "Nat") (TyCon "Bool"))
        (TyArr (TyCon "Nat") (TyCon "Bool"))
        (TyArr (TyCon "Nat") (TyCon "Bool"))
    )
  , ( "meet: TyArr ≢ TyArr — argument mismatch"
    , expectMismatch
        (TyArr (TyCon "Nat") (TyCon "Bool"))
        (TyArr (TyCon "Int") (TyCon "Bool"))
    )
  , ( "meet: TyArr ≢ TyArr — result mismatch"
    , expectMismatch
        (TyArr (TyCon "Nat") (TyCon "Bool"))
        (TyArr (TyCon "Nat") (TyCon "Int"))
    )
  , ( "meet: TyApp ≡ TyApp — congruent children"
    , expectOK
        (TyApp (TyCon "List") (TyCon "Nat"))
        (TyApp (TyCon "List") (TyCon "Nat"))
        (TyApp (TyCon "List") (TyCon "Nat"))
    )
  , ( "meet: TyApp ≢ TyApp — different constructor"
    , expectMismatch
        (TyApp (TyCon "List") (TyCon "Nat"))
        (TyApp (TyCon "Maybe") (TyCon "Nat"))
    )
  , ( "meet: TyVar ≡ TyVar — same name, same path (Stern-Gerlach equal)"
    , let pa = Path [PsProgDecl 0, PsDataParam 0]
      in expectOK (TyVar "a" pa) (TyVar "a" pa) (TyVar "a" pa)
    )
  , ( "meet: TyVar ≢ TyVar — same name, different paths (Stern-Gerlach split)"
    , let pa1 = Path [PsProgDecl 0, PsDataParam 0]
          pa2 = Path [PsProgDecl 1, PsDataParam 0]
      in expectMismatch (TyVar "a" pa1) (TyVar "a" pa2)
    )
  , ( "meet: head mismatch — TyArr vs TyApp"
    , expectMismatch
        (TyArr (TyCon "Nat") (TyCon "Bool"))
        (TyApp (TyCon "List") (TyCon "Nat"))
    )
  ]

-- | Build two 'TyProc's from 'TyExpr's, unify them, and check the
--   extracted result against the expected type.
expectOK :: TyExpr -> TyExpr -> TyExpr -> IO Bool
expectOK t1 t2 want =
  case meet (tyToProc t1) (tyToProc t2) of
    Left err -> reportFail $ "meet failed: " <> show err
    Right p  ->
      let got = procToTy p
      in if got == want
           then pure True
           else reportFail $
             "expected " <> show want <> "\n  got " <> show got

expectMismatch :: TyExpr -> TyExpr -> IO Bool
expectMismatch t1 t2 = case meet (tyToProc t1) (tyToProc t2) of
  Left (TyMismatch _ _) -> pure True
  Left err -> reportFail $
    "expected TyMismatch, got " <> show err
  Right p -> reportFail $
    "expected TyMismatch, got success: " <> show (procToTy p)

reportFail :: String -> IO Bool
reportFail msg = putStrLn ("    " <> msg) >> pure False
