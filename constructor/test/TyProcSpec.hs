{-# LANGUAGE OverloadedStrings #-}

-- | Direct tests for 'Constructor.TyProc.meet'.
--
--   Unlike 'TinfSpec' / 'HypTinfSpec', these exercise the algebra
--   without going through a 'Lang' carrier or the parser — `meet` is
--   built as commit-5 *apparatus* without a carrier-level customer
--   yet, so the tests build 'TyProc's directly from 'TyExpr's via
--   'tyToProc' and call `meet` pointwise.
module TyProcSpec (tests) where

import Constructor.HyperLite (hPure)
import Constructor.Level (Lv (..))
import Constructor.Path (Path (..), PathStep (..))
import Constructor.Tinf (TyErr (..))
import Constructor.TyExpr (TyExpr (..))
import Constructor.TyProc
  ( MetaId (..)
  , Subst
  , TyProc
  , TyView (..)
  , emptySubst
  , materialize
  , meet
  , mkMeta
  , tyToProc
  , unionSubst
  )
import qualified Data.Map.Strict as Map

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

    -- --- Metavariable apparatus ---------------------------------------
  , ( "meet (meta ≡ concrete): subst binds the meta"
    , let bp = Path [PsProgDecl 0, PsDataParam 0]
          up = Path [PsProgDecl 3]
          meta = mkMeta bp up
          target = TyCon "Nat" natP
      in expectMeetThenMaterialize
           emptySubst meta (tyToProc target)
           meta target
    )
  , ( "meet (concrete ≡ meta): symmetric — subst binds the meta"
    , let bp = Path [PsProgDecl 0, PsDataParam 0]
          up = Path [PsProgDecl 3]
          meta = mkMeta bp up
          target = TyCon "Bool" boolP
      in expectMeetThenMaterialize
           emptySubst (tyToProc target) meta
           meta target
    )
  , ( "meet (meta1 ≡ meta2): one redirects to the other"
    , let bp = Path [PsProgDecl 0, PsDataParam 0]
          m1 = mkMeta bp (Path [PsProgDecl 3])
          m2 = mkMeta bp (Path [PsProgDecl 4])
      in do
        case meet emptySubst m1 m2 of
          Left err -> reportFail $ "meet failed: " <> show err
          Right s -> case materialize s m1 of
            -- Both metas remain unresolved structurally — the chain
            -- m1 → m2 leads to an unbound m2.  Materialize surfaces
            -- TyUnresolvedMeta for m2; binding either tip resolves
            -- the whole chain (the redirect property the design
            -- requires).
            Left (TyUnresolvedMeta _ _) -> pure True
            Left err -> reportFail $
              "expected unresolved redirect chain, got error " <> show err
            Right got -> reportFail $
              "expected unresolved redirect chain, got resolved " <> show got
    )
  , ( "redirect chain: meet m1 m2; meet m2 concrete; materialize m1 → concrete"
    , let bp = Path [PsProgDecl 0, PsDataParam 0]
          m1 = mkMeta bp (Path [PsProgDecl 3])
          m2 = mkMeta bp (Path [PsProgDecl 4])
          c  = tyToProc (TyCon "Bool" boolP)
      in do
        case meet emptySubst m1 m2 of
          Left err -> reportFail $ "first meet failed: " <> show err
          Right s1 -> case meet s1 m2 c of
            Left err -> reportFail $ "second meet failed: " <> show err
            Right s2 -> case materialize s2 m1 of
              Right got
                | got == TyCon "Bool" boolP -> pure True
                | otherwise -> reportFail $
                    "expected TyCon \"Bool\" boolP, got " <> show got
              Left err -> reportFail $
                "materialize after chain failed: " <> show err
    )
  , ( "conflict: meet m Bool then meet m Int → TyMismatch"
    , let bp = Path [PsProgDecl 0, PsDataParam 0]
          m  = mkMeta bp (Path [PsProgDecl 3])
          b  = tyToProc (TyCon "Bool" boolP)
          i  = tyToProc (TyCon "Int" intP)
      in do
        case meet emptySubst m b of
          Left err -> reportFail $ "first meet failed: " <> show err
          Right s1 -> case meet s1 m i of
            Left (TyMismatch _ _) -> pure True
            Left err -> reportFail $
              "expected TyMismatch, got error " <> show err
            Right _ -> reportFail
              "expected TyMismatch, got success"
    )
  , ( "compound: meet (List m) (List Nat) propagates m := Nat"
    , let bp      = Path [PsProgDecl 0, PsDataParam 0]
          up      = Path [PsProgDecl 3]
          m       = mkMeta bp up
          listM   = hPure (TyAppV (tyToProc (TyCon "List" listP)) m)
          listNat = tyToProc (TyApp (TyCon "List" listP) (TyCon "Nat" natP))
      in do
        case meet emptySubst listM listNat of
          Left err -> reportFail $ "meet failed: " <> show err
          Right s -> case materialize s m of
            Right got
              | got == TyCon "Nat" natP -> pure True
              | otherwise -> reportFail $
                  "expected TyCon \"Nat\" natP, got " <> show got
            Left err -> reportFail $
              "materialize failed: " <> show err
    )
    -- --- Structural occurs check ---------------------------------
  , ( "occurs: meet m (List m) rejects as TyOccursCheck"
    , -- The classical Robinson trap.  Binding m := List m would
      -- produce the infinite type List (List (List …)); 'meet'
      -- must reject before recording the binding.
      let bp = Path [PsProgDecl 0, PsDataParam 0]
          up = Path [PsProgDecl 3]
          m  = mkMeta bp up
          listM = hPure (TyAppV (tyToProc (TyCon "List" listP)) m)
      in case meet emptySubst m listM of
        Left (TyOccursCheck bp' up')
          | bp' == bp && up' == up -> pure True
          | otherwise -> reportFail $
              "TyOccursCheck path mismatch: got bp=" <> show bp' <>
              " up=" <> show up'
        Left err -> reportFail $
          "expected TyOccursCheck, got: " <> show err
        Right _ -> reportFail
          "expected TyOccursCheck, got success (cyclic binding accepted!)"
    )
  , ( "occurs: meet m (Nat -> m) rejects as TyOccursCheck (arrow path)"
    , let bp = Path [PsProgDecl 0, PsDataParam 0]
          up = Path [PsProgDecl 3]
          m  = mkMeta bp up
          natArrM = hPure (TyArrV (tyToProc (TyCon "Nat" natP)) m)
      in case meet emptySubst m natArrM of
        Left (TyOccursCheck _ _) -> pure True
        Left err -> reportFail $
          "expected TyOccursCheck, got: " <> show err
        Right _ -> reportFail
          "expected TyOccursCheck on Nat -> m, got success"
    )
  , ( "occurs: transitive — m1 already bound to (App List m2), meet m2 m1 rejects"
    , -- After binding m1 := List m2, meeting m2 with m1 (which
      -- resolves to List m2 via Subst) would bind m2 := List m2 —
      -- the occurs check must chase through the Subst.
      let bp = Path [PsProgDecl 0, PsDataParam 0]
          m1 = mkMeta bp (Path [PsProgDecl 3])
          m2 = mkMeta bp (Path [PsProgDecl 4])
          listM2 = hPure (TyAppV (tyToProc (TyCon "List" listP)) m2)
      in case meet emptySubst m1 listM2 of
        Left err -> reportFail $ "first meet failed: " <> show err
        Right s1 -> case meet s1 m2 m1 of
          Left (TyOccursCheck _ _) -> pure True
          Left err -> reportFail $
            "expected TyOccursCheck (transitive), got: " <> show err
          Right _ -> reportFail
            "expected TyOccursCheck (transitive), got success"
    )

    -- --- unionSubst: occurs-checked combination of refinements ------
    -- The v0.7.0 soundness fix.  Narrowing combines two independently-
    -- searched sides' refinements; raw 'Map.union' would fuse a cycle
    -- that 'resolveView' loops on.  'unionSubst' must reject it.
  , ( "unionSubst: two-side cycle ?a := S ?b ∪ ?b := S ?a → TyOccursCheck (no loop)"
    , let bp1 = Path [PsProgDecl 0, PsDataParam 0]
          bp2 = Path [PsProgDecl 1, PsDataParam 0]
          a   = MetaId bp1 bp1
          b   = MetaId bp2 bp2
          sOf x = TyAppV (hPure (TyConV "S" natP Z)) (hPure x)
          sub1 = Map.singleton a (sOf (TyMetaV b))
          sub2 = Map.singleton b (sOf (TyMetaV a))
      in case unionSubst emptySubst sub1 >>= flip unionSubst sub2 of
           Left (TyOccursCheck _ _) -> pure True
           Left err -> reportFail $
             "expected TyOccursCheck, got: " <> show err
           Right _ -> reportFail
             "expected TyOccursCheck, got success (cycle accepted!)"
    )
  , ( "unionSubst: disjoint refinements ?a := Nat ∪ ?b := Bool merge cleanly"
    , let a    = MetaId (Path [PsProgDecl 0, PsDataParam 0]) (Path [PsProgDecl 3])
          b    = MetaId (Path [PsProgDecl 1, PsDataParam 0]) (Path [PsProgDecl 4])
          sub1 = Map.singleton a (TyConV "Nat" natP Z)
          sub2 = Map.singleton b (TyConV "Bool" boolP Z)
      in case unionSubst emptySubst sub1 >>= flip unionSubst sub2 of
           Right s ->
             case ( materialize s (hPure (TyMetaV a))
                  , materialize s (hPure (TyMetaV b)) ) of
               (Right (TyCon "Nat" _), Right (TyCon "Bool" _)) -> pure True
               other -> reportFail $ "unexpected materialize: " <> show other
           Left err -> reportFail $ "expected success, got: " <> show err
    )
  , ( "unionSubst: same-key conflict ?a := Nat vs ?a := Bool → honest TyMismatch"
    , let a    = MetaId (Path [PsProgDecl 0, PsDataParam 0]) (Path [PsProgDecl 3])
          sub1 = Map.singleton a (TyConV "Nat" natP Z)
          sub2 = Map.singleton a (TyConV "Bool" boolP Z)
      in case unionSubst emptySubst sub1 >>= flip unionSubst sub2 of
           Left (TyMismatch _ _) -> pure True
           Left err -> reportFail $
             "expected TyMismatch, got: " <> show err
           Right _ -> reportFail
             "expected TyMismatch, got success (silent wrong-commit!)"
    )
  ]

-- | Build two 'TyProc's from 'TyExpr's, unify them under
--   'emptySubst', and check the extracted result against the
--   expected type.
expectOK :: TyExpr -> TyExpr -> TyExpr -> IO Bool
expectOK t1 t2 want =
  case meet emptySubst (tyToProc t1) (tyToProc t2) of
    Left err -> reportFail $ "meet failed: " <> show err
    Right s -> case materialize s (tyToProc t1) of
      Left err -> reportFail $ "materialize failed: " <> show err
      Right got
        | got == want -> pure True
        | otherwise -> reportFail $
            "expected " <> show want <> "\n  got " <> show got

expectMismatch :: TyExpr -> TyExpr -> IO Bool
expectMismatch t1 t2 = case meet emptySubst (tyToProc t1) (tyToProc t2) of
  Left (TyMismatch _ _) -> pure True
  Left err -> reportFail $
    "expected TyMismatch, got " <> show err
  Right _ -> reportFail "expected TyMismatch, got success"

-- | Run a 'meet' from an explicit pre-state, then 'materialize' a
--   nominated process, and check the result.
expectMeetThenMaterialize
  :: Subst -> TyProc -> TyProc -> TyProc -> TyExpr -> IO Bool
expectMeetThenMaterialize s p1 p2 probe want =
  case meet s p1 p2 of
    Left err -> reportFail $ "meet failed: " <> show err
    Right s' -> case materialize s' probe of
      Left err -> reportFail $ "materialize failed: " <> show err
      Right got
        | got == want -> pure True
        | otherwise -> reportFail $
            "expected " <> show want <> "\n  got " <> show got

reportFail :: String -> IO Bool
reportFail msg = putStrLn ("    " <> msg) >> pure False
