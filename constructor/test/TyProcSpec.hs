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

-- | Stand-in def-paths for the named tycons under test.  Mirrors what
--   the parser would emit if these were declared at the given
--   top-level positions.
natP, boolP, intP, listP, maybeP :: Path
natP   = Path [PsProgDecl 0]
boolP  = Path [PsProgDecl 1]
intP   = Path [PsProgDecl 2]
listP  = Path [PsProgDecl 3]
maybeP = Path [PsProgDecl 4]

tests :: [(String, IO Bool)]
tests =
  [ ( "meet: TyCon ≡ TyCon (same name, same path)"
    , expectOK
        (TyCon "Nat" natP)
        (TyCon "Nat" natP)
        (TyCon "Nat" natP)
    )
  , ( "meet: TyCon ≢ TyCon (different name)"
    , expectMismatch
        (TyCon "Nat" natP)
        (TyCon "Bool" boolP)
    )
  , ( "meet: TyCon ≢ TyCon (same name, different paths) — \
       \def-path Stern-Gerlach"
    , let p1 = Path [PsProgDecl 0]
          p2 = Path [PsProgDecl 1]
      in expectMismatch (TyCon "Bool" p1) (TyCon "Bool" p2)
    )
  , ( "meet: TyArr ≡ TyArr — congruent children"
    , expectOK
        (TyArr (TyCon "Nat" natP) (TyCon "Bool" boolP))
        (TyArr (TyCon "Nat" natP) (TyCon "Bool" boolP))
        (TyArr (TyCon "Nat" natP) (TyCon "Bool" boolP))
    )
  , ( "meet: TyArr ≢ TyArr — argument mismatch"
    , expectMismatch
        (TyArr (TyCon "Nat" natP) (TyCon "Bool" boolP))
        (TyArr (TyCon "Int" intP) (TyCon "Bool" boolP))
    )
  , ( "meet: TyArr ≢ TyArr — result mismatch"
    , expectMismatch
        (TyArr (TyCon "Nat" natP) (TyCon "Bool" boolP))
        (TyArr (TyCon "Nat" natP) (TyCon "Int" intP))
    )
  , ( "meet: TyApp ≡ TyApp — congruent children"
    , expectOK
        (TyApp (TyCon "List" listP) (TyCon "Nat" natP))
        (TyApp (TyCon "List" listP) (TyCon "Nat" natP))
        (TyApp (TyCon "List" listP) (TyCon "Nat" natP))
    )
  , ( "meet: TyApp ≢ TyApp — different constructor"
    , expectMismatch
        (TyApp (TyCon "List" listP) (TyCon "Nat" natP))
        (TyApp (TyCon "Maybe" maybeP) (TyCon "Nat" natP))
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
        (TyArr (TyCon "Nat" natP) (TyCon "Bool" boolP))
        (TyApp (TyCon "List" listP) (TyCon "Nat" natP))
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
