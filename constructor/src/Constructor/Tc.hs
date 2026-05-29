{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

-- | Constraint generation as a separate Lang HKT pass.
--
--   Builds the substrate's constraint state ('Sheet') plus a
--   declared-name → 'Place' map, then hands both off to a solver.
--   No syntactic 'Tree' is constructed by this carrier — consumers that
--   want one parse at @r ~ Tree@ separately.  The 'Lang' instance never
--   pattern-matches on a 'Tree' value (it never sees one), and the
--   solver consumes the 'TcResult' record directly without any
--   tree-walking.
--
--   This is the "Sheet-driven" baseline carrier in Architecture A: it
--   does its unification work imperatively through 'Sheet.unify' /
--   'Sheet.pin'.  The companion experimental carrier (Architecture B,
--   hyperfunction-driven) will live in its own module and produce the
--   same 'TcResult' shape for parity testing.
module Constructor.Tc
  ( TcVal (..)
  , TcResult (..)
  , Tc
  , tcProgram
  , solveLevels
  ) where

import Constructor.Level (Lv (..), starLevel)
import Constructor.LevelInfer (LevelMap, LvErr (..))
import Constructor.Sheet
import Constructor.Sort (Sort (..))
import Constructor.Syntax (Lang (..), Name)
import Data.Kind (Type)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

-- | Carrier value: exposes the 'Place' that each sort with one
--   carries.  Other 'Lang' methods read their children's places by
--   projecting this — no syntactic structure to inspect.
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

-- | Solver-facing output: the substrate's resolved constraints, plus
--   the bound-name map collected during the pass.
data TcResult = TcResult
  { tcResultSheet :: !(Sheet Lv)
  , tcResultNames :: !(Map Name Place)
  }

newtype Tc (a :: Sort -> Type) (s :: Sort) = Tc
  { runTc :: TcEnv -> Either LvErr (TcVal s, TcEnv) }

tcProgram :: Tc a 'SProg -> Either LvErr TcResult
tcProgram p = do
  (_, env) <- runTc p emptyTcEnv
  pure (TcResult (tcEnvSheet env) (tcEnvNames env))

-- ----------------------------------------------------------------------
-- The Lang instance.
-- ----------------------------------------------------------------------

predLv :: Lv -> Maybe Lv
predLv Z     = Nothing
predLv (S n) = Just n

mergeLv :: Lv -> Lv -> Either LvErr Lv
mergeLv a b
  | a == b    = Right a
  | otherwise = Left (LevelTear a b)

bind :: Name -> Place -> TcEnv -> Either LvErr TcEnv
bind n p env
  | Map.member n (tcEnvNames env) = Left (Duplicate n)
  | otherwise = Right env { tcEnvNames = Map.insert n p (tcEnvNames env) }

threadDecls :: [Tc a 'SDecl] -> TcEnv -> Either LvErr TcEnv
threadDecls []     env = Right env
threadDecls (d:ds) env = do
  (_, env1) <- runTc d env
  threadDecls ds env1

instance Lang Tc where
  prog _ann ds = Tc $ \env -> do
    env' <- threadDecls ds env
    pure (TcVProg, env')

  dataDecl _ann n e ds = Tc $ \env -> do
    (ev, env1) <- runTc e env
    let pe = tcExprPlace ev
        (mLe, sheet1) = levelOf pe (tcEnvSheet env1)
        env1' = env1 { tcEnvSheet = sheet1 }
    le <- maybe (Left UnpinnedLevel) Right mLe
    ln <- maybe (Left (DataAnnotationTooLow n le)) Right (predLv le)
    let (pn, sheet2) = freshPlace (tcEnvSheet env1')
    sheet3 <- pin mergeLv pn ln sheet2
    env2 <- bind n pn (env1' { tcEnvSheet = sheet3, tcEnvParent = Just pn })
    env3 <- threadDecls ds env2
    pure (TcVDecl pn, env3 { tcEnvParent = tcEnvParent env1' })

  ctorDecl _ann n t = Tc $ \env -> do
    parent <- maybe (Left (CtorOutsideData n)) Right (tcEnvParent env)
    (tv, env1) <- runTc t env
    let pt = tcExprPlace tv
    sheet1 <- unify mergeLv pt parent (tcEnvSheet env1)
    let (mLp, sheet2) = levelOf parent sheet1
    lp <- maybe (Left UnpinnedLevel) Right mLp
    lc <- maybe (Left (DataAnnotationTooLow n lp)) Right (predLv lp)
    let (pc, sheet3) = freshPlace sheet2
    sheet4 <- pin mergeLv pc lc sheet3
    env2 <- bind n pc (env1 { tcEnvSheet = sheet4 })
    pure (TcVDecl pc, env2)

  var _ann x = Tc $ \env -> case Map.lookup x (tcEnvNames env) of
    Just p  -> Right (TcVExpr p, env)
    Nothing -> Left (Unbound x)

  star _ann w = Tc $ \env -> do
    let (p, sheet1) = freshPlace (tcEnvSheet env)
    sheet2 <- pin mergeLv p (starLevel w) sheet1
    pure (TcVExpr p, env { tcEnvSheet = sheet2 })

  arr _ann a b = Tc $ \env -> do
    (av, env1) <- runTc a env
    (bv, env2) <- runTc b env1
    let pa = tcExprPlace av
        pb = tcExprPlace bv
        (parr, sheet0) = freshPlace (tcEnvSheet env2)
    sheet1 <- unify mergeLv pa pb sheet0
    sheet2 <- unify mergeLv parr pa sheet1
    pure (TcVExpr parr, env2 { tcEnvSheet = sheet2 })

-- ----------------------------------------------------------------------
-- Solver.  Pure record-projection — no syntactic traversal.
-- ----------------------------------------------------------------------

solveLevels :: TcResult -> Either LvErr LevelMap
solveLevels r =
  Map.fromList <$> traverse (resolveOne (tcResultSheet r))
                            (Map.toList (tcResultNames r))

resolveOne :: Sheet Lv -> (Name, Place) -> Either LvErr (Name, Lv)
resolveOne sheet (n, p) = case fst (levelOf p sheet) of
  Just lv -> Right (n, lv)
  Nothing -> Left UnpinnedLevel
