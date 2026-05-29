{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}

-- | Constraint generation as a separate Lang HKT pass, with a
--   simultaneously-produced polymorphic finally-tagless term decorated
--   by inferred level annotations.
--
--   Each method does its analysis work AND constructs a polymorphic
--   @r LvAnnot s@ term in its third tuple slot.  The caller of
--   'tcRunWith' picks @r@ — Tree for inspection, Pp for
--   pretty-printing, or any other 'Lang' instance — and gets back both
--   the analysis result ('TcResult') and a structurally identical
--   carrier value with the inferred levels baked into each node.
--
--   The 'forall r.' inside the 'Tc' newtype's record field needs
--   'ImpredicativeTypes'.  GHC 9.10's QuickLook handles it cleanly.
--   Escape hatch if we ever need to drop the extension: hoist @r@ to a
--   parameter of 'Tc' (giving 'Tc r a s') and make the instance
--   @instance Lang r => Lang (Tc r)@.  The trade-off is that @r@
--   becomes a parse-time choice rather than an extraction-time choice;
--   re-specialisation then needs a Tree intermediate.
module Constructor.Tc
  ( LvAnnot (..)
  , TcVal (..)
  , TcResult (..)
  , Tc
  , Discard
  , tcProgram
  , tcRunWith
  , solveLevels
  ) where

import Constructor.Level (Lv (..), addOffset, starLevel)
import Constructor.LevelInfer (LevelMap, LvErr (..))
import Constructor.Sheet
import Constructor.Sort (Sort (..))
import Constructor.Syntax (Lang (..), Name)
import Data.Kind (Type)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

-- | Annotation carrying the inferred level at each node.  Specialise the
--   polymorphic term in 'tcRunWith''s result at any @Lang r@ to see it
--   threaded through that carrier.
data LvAnnot (s :: Sort) where
  LvAExpr :: !Lv -> LvAnnot 'SExpr
  LvADecl :: !Lv -> LvAnnot 'SDecl
  LvAProg ::         LvAnnot 'SProg

deriving instance Show (LvAnnot s)
deriving instance Eq (LvAnnot s)

-- | Carrier value: exposes the substrate 'Place' for sorts that carry one.
data TcVal (s :: Sort) where
  TcVExpr :: !Place -> TcVal 'SExpr
  TcVDecl :: !Place -> TcVal 'SDecl
  TcVProg ::           TcVal 'SProg

tcExprPlace :: TcVal 'SExpr -> Place
tcExprPlace (TcVExpr p) = p

data TcEnv = TcEnv
  { tcEnvSheet  :: !(Sheet Lv)
  , tcEnvNames  :: !(Map Name Place)
  , tcEnvParent :: !(Maybe Place)
  } deriving Show

emptyTcEnv :: TcEnv
emptyTcEnv = TcEnv emptySheet Map.empty Nothing

-- | Solver-facing analysis result.
data TcResult = TcResult
  { tcResultSheet :: !(Sheet Lv)
  , tcResultNames :: !(Map Name Place)
  }

-- | The constraint-gathering carrier.  Phantom in the user-supplied
--   annotation @a@; the third tuple element is a polymorphic Lang term
--   over the inferred 'LvAnnot' annotations.
newtype Tc (a :: Sort -> Type) (s :: Sort) = Tc
  { runTc :: forall r. Lang r =>
             TcEnv -> Either LvErr (TcVal s, TcEnv, r LvAnnot s)
  }

-- | A trivial Lang instance that throws all inputs away.  Used by
--   'tcProgram' to specialise the polymorphic term slot when we don't
--   need it.
newtype Discard (a :: Sort -> Type) (s :: Sort) = Discard ()

instance Lang Discard where
  prog _ _           = Discard ()
  dataDecl _ _ _ _ _ = Discard ()
  ctorDecl _ _ _     = Discard ()
  var _ _            = Discard ()
  star _ _           = Discard ()
  arr _ _ _          = Discard ()
  forallLv _ _ _ _   = Discard ()
  starVar _ _ _ _    = Discard ()
  app _ _ _          = Discard ()

-- | Analysis only: specialise the polymorphic term at 'Discard' and
--   discard it.
tcProgram :: Tc a 'SProg -> Either LvErr TcResult
tcProgram p = do
  (_, env, _ :: Discard LvAnnot 'SProg) <- runTc p emptyTcEnv
  pure (TcResult (tcEnvSheet env) (tcEnvNames env))

-- | Analysis + polymorphic LvAnnot-decorated term.  Caller supplies the
--   carrier @r@ at the call site.
tcRunWith
  :: forall r a. Lang r
  => Tc a 'SProg
  -> Either LvErr (TcResult, r LvAnnot 'SProg)
tcRunWith p = do
  (_, env, term) <- runTc p emptyTcEnv
  pure (TcResult (tcEnvSheet env) (tcEnvNames env), term)

-- ----------------------------------------------------------------------
-- The Lang instance.
-- ----------------------------------------------------------------------

predLv :: Lv -> Maybe Lv
predLv Z        = Nothing
predLv (S n)    = Just n
predLv (LVar _) = Nothing   -- polymorphic levels: unsupported here; forallLv's
                            -- error default will fire first in practice

mergeLv :: Lv -> Lv -> Either LvErr Lv
mergeLv a b
  | a == b    = Right a
  | otherwise = Left (LevelTear a b)

bind :: Name -> Place -> TcEnv -> Either LvErr TcEnv
bind n p env
  | Map.member n (tcEnvNames env) = Left (Duplicate n)
  | otherwise = Right env { tcEnvNames = Map.insert n p (tcEnvNames env) }

threadDecls
  :: forall r a. Lang r
  => [Tc a 'SDecl]
  -> TcEnv
  -> Either LvErr ([r LvAnnot 'SDecl], TcEnv)
threadDecls []     env = Right ([], env)
threadDecls (d:ds) env = do
  (_, env1, t)  <- runTc d env
  (ts, env2)    <- threadDecls ds env1
  pure (t : ts, env2)

instance Lang Tc where
  prog _ann ds = Tc $ \env -> do
    (ts, env') <- threadDecls ds env
    pure (TcVProg, env', prog LvAProg ts)

  dataDecl _ann n params e ds = Tc $ \env -> do
    (ev, env1, polyE) <- runTc e env
    let pe = tcExprPlace ev
        (mLe, sheet1) = levelOf pe (tcEnvSheet env1)
        env1' = env1 { tcEnvSheet = sheet1 }
    le <- maybe (Left UnpinnedLevel) Right mLe
    ln <- maybe (Left (DataAnnotationTooLow n le)) Right (predLv le)
    let (pn, sheet2) = freshPlace (tcEnvSheet env1')
    sheet3 <- pin mergeLv pn ln sheet2
    env2  <- bind n pn (env1' { tcEnvSheet = sheet3, tcEnvParent = Just pn })
    (polys, env3) <- threadDecls ds env2
    pure ( TcVDecl pn
         , env3 { tcEnvParent = tcEnvParent env1' }
         , dataDecl (LvADecl ln) n params polyE polys
         )

  ctorDecl _ann n t = Tc $ \env -> do
    parent <- maybe (Left (CtorOutsideData n)) Right (tcEnvParent env)
    (tv, env1, polyT) <- runTc t env
    let pt = tcExprPlace tv
    sheet1 <- unify mergeLv pt parent (tcEnvSheet env1)
    let (mLp, sheet2) = levelOf parent sheet1
    lp <- maybe (Left UnpinnedLevel) Right mLp
    lc <- maybe (Left (DataAnnotationTooLow n lp)) Right (predLv lp)
    let (pc, sheet3) = freshPlace sheet2
    sheet4 <- pin mergeLv pc lc sheet3
    env2 <- bind n pc (env1 { tcEnvSheet = sheet4 })
    pure (TcVDecl pc, env2, ctorDecl (LvADecl lc) n polyT)

  var _ann x = Tc $ \env -> case Map.lookup x (tcEnvNames env) of
    Just p  ->
      let (mLv, _) = levelOf p (tcEnvSheet env)
      in case mLv of
        Just lv -> Right (TcVExpr p, env, var (LvAExpr lv) x)
        Nothing -> Left UnpinnedLevel
    Nothing -> Left (Unbound x)

  star _ann w = Tc $ \env -> do
    let (p, sheet1) = freshPlace (tcEnvSheet env)
    sheet2 <- pin mergeLv p (starLevel w) sheet1
    let lv = starLevel w
    pure (TcVExpr p, env { tcEnvSheet = sheet2 }, star (LvAExpr lv) w)

  arr _ann a b = Tc $ \env -> do
    (av, env1, polyA) <- runTc a env
    (bv, env2, polyB) <- runTc b env1
    let pa = tcExprPlace av
        pb = tcExprPlace bv
        (parr, sheet0) = freshPlace (tcEnvSheet env2)
    sheet1 <- unify mergeLv pa pb sheet0
    sheet2 <- unify mergeLv parr pa sheet1
    let (mLv, sheet3) = levelOf parr sheet2
    lv <- maybe (Left UnpinnedLevel) Right mLv
    pure (TcVExpr parr, env2 { tcEnvSheet = sheet3 }, arr (LvAExpr lv) polyA polyB)

  -- The parser resolved the binder + use names to 'Path's; the carrier
  -- just uses them.  No internal binder env, no counter.
  forallLv _ann name binderPath body = Tc $ \env -> do
    (bv, env1, polyBody) <- runTc body env
    let pBody = tcExprPlace bv
        (mLv, sheet') = levelOf pBody (tcEnvSheet env1)
    lv <- maybe (Left UnpinnedLevel) Right mLv
    pure ( TcVExpr pBody
         , env1 { tcEnvSheet = sheet' }
         , forallLv (LvAExpr lv) name binderPath polyBody
         )

  starVar _ann name binderPath offset = Tc $ \env -> do
    let lv = addOffset (LVar binderPath) offset
        (p, sheet1) = freshPlace (tcEnvSheet env)
    sheet2 <- pin mergeLv p lv sheet1
    pure (TcVExpr p, env { tcEnvSheet = sheet2 }, starVar (LvAExpr lv) name binderPath offset)

-- ----------------------------------------------------------------------
-- Solver.  Pure record-projection over 'TcResult'.
-- ----------------------------------------------------------------------

solveLevels :: TcResult -> Either LvErr LevelMap
solveLevels r =
  Map.fromList <$> traverse (resolveOne (tcResultSheet r))
                            (Map.toList (tcResultNames r))

resolveOne :: Sheet Lv -> (Name, Place) -> Either LvErr (Name, Lv)
resolveOne sheet (n, p) = case fst (levelOf p sheet) of
  Just lv -> Right (n, lv)
  Nothing -> Left UnpinnedLevel
