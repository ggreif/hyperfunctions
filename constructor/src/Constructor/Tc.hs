{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StandaloneDeriving #-}

-- | Constraint generation as a separate Lang HKT pass.
--
--   Walks the program identical to 'Lvl', allocating 'Place's on the
--   substrate and emitting 'unify' / 'pin' constraints — but instead of
--   collapsing to a 'LevelMap', it preserves an annotated AST
--   ('Tree' 'TcAnn') alongside the final 'Sheet'.  The pair
--   @(Tree TcAnn, Sheet)@ is the input that downstream consumers (a
--   solver, a pretty-printer, an error reporter) walk; for v0 the
--   trivial solver 'solveLevels' projects back to a 'LevelMap'.
--
--   Tc is phantom in the user-supplied annotation @a@: it produces its
--   own internal 'TcAnn' so that downstream passes have a single,
--   uniform decoration to read.  Path-tracking can be retrofitted later
--   on top of this carrier without changing its shape.
module Constructor.Tc
  ( TcAnn (..)
  , TcResult (..)
  , Tc
  , tcProgram
  , solveLevels
  ) where

import Constructor.AST (Tree (..))
import Constructor.Level (Lv (..), starLevel)
import Constructor.LevelInfer (LevelMap, LvErr (..))
import Constructor.Sheet
import Constructor.Sort (Sort (..))
import Constructor.Syntax (Lang (..), Name)
import Data.Kind (Type)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

-- | Per-sort annotation: 'SExpr' nodes carry their 'Place'; 'SDecl'
--   carries the declared name's 'Place'.
data TcAnn (s :: Sort) where
  TcAExpr :: !Place -> TcAnn 'SExpr
  TcADecl :: !Place -> TcAnn 'SDecl
  TcAProg :: TcAnn 'SProg

deriving instance Show (TcAnn s)
deriving instance Eq (TcAnn s)

data TcEnv = TcEnv
  { tcEnvSheet  :: !(Sheet Lv)
  , tcEnvNames  :: !(Map Name Place)
  , tcEnvParent :: !(Maybe Place)
  } deriving Show

emptyTcEnv :: TcEnv
emptyTcEnv = TcEnv emptySheet Map.empty Nothing

-- | Output bundle: annotated AST + final 'Sheet' state.
data TcResult (s :: Sort) = TcResult
  { tcResultTree  :: Tree TcAnn s
  , tcResultSheet :: Sheet Lv
  }

-- | Constraint-generation carrier.  Phantom in @a@.
newtype Tc (a :: Sort -> Type) (s :: Sort) = Tc
  { runTc :: TcEnv -> Either LvErr (Tree TcAnn s, TcEnv) }

-- | Top-level entry: parses straight into 'TcResult' via
--   @parseProgram @Tc@.
tcProgram :: Tc a 'SProg -> Either LvErr (TcResult 'SProg)
tcProgram p = do
  (tree, env) <- runTc p emptyTcEnv
  pure (TcResult tree (tcEnvSheet env))

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

threadDecls
  :: [Tc a 'SDecl]
  -> TcEnv
  -> Either LvErr ([Tree TcAnn 'SDecl], TcEnv)
threadDecls []     env = Right ([], env)
threadDecls (d:ds) env = do
  (t, env1)  <- runTc d env
  (ts, env2) <- threadDecls ds env1
  pure (t : ts, env2)

exprPlace :: Tree TcAnn 'SExpr -> Place
exprPlace = \case
  Var  (TcAExpr p) _   -> p
  Star (TcAExpr p) _   -> p
  Arr  (TcAExpr p) _ _ -> p

instance Lang Tc where
  prog _ann ds = Tc $ \env -> do
    (ts, env') <- threadDecls ds env
    pure (Prog TcAProg ts, env')

  dataDecl _ann n e ds = Tc $ \env -> do
    (te, env1) <- runTc e env
    let pe = exprPlace te
        (mLe, sheet1) = levelOf pe (tcEnvSheet env1)
        env1' = env1 { tcEnvSheet = sheet1 }
    le <- maybe (Left UnpinnedLevel) Right mLe
    ln <- maybe (Left (DataAnnotationTooLow n le)) Right (predLv le)
    let (pn, sheet2) = freshPlace (tcEnvSheet env1')
    sheet3 <- pin mergeLv pn ln sheet2
    env2 <- bind n pn (env1' { tcEnvSheet = sheet3, tcEnvParent = Just pn })
    (ts, env3) <- threadDecls ds env2
    pure (DataDecl (TcADecl pn) n te ts, env3 { tcEnvParent = tcEnvParent env1' })

  ctorDecl _ann n t = Tc $ \env -> do
    parent <- maybe (Left (CtorOutsideData n)) Right (tcEnvParent env)
    (tt, env1) <- runTc t env
    let pt = exprPlace tt
    sheet1 <- unify mergeLv pt parent (tcEnvSheet env1)
    let (mLp, sheet2) = levelOf parent sheet1
    lp <- maybe (Left UnpinnedLevel) Right mLp
    lc <- maybe (Left (DataAnnotationTooLow n lp)) Right (predLv lp)
    let (pc, sheet3) = freshPlace sheet2
    sheet4 <- pin mergeLv pc lc sheet3
    env2 <- bind n pc (env1 { tcEnvSheet = sheet4 })
    pure (CtorDecl (TcADecl pc) n tt, env2)

  var _ann x = Tc $ \env -> case Map.lookup x (tcEnvNames env) of
    Just p  -> Right (Var (TcAExpr p) x, env)
    Nothing -> Left (Unbound x)

  star _ann w = Tc $ \env -> do
    let (p, sheet1) = freshPlace (tcEnvSheet env)
    sheet2 <- pin mergeLv p (starLevel w) sheet1
    pure (Star (TcAExpr p) w, env { tcEnvSheet = sheet2 })

  arr _ann a b = Tc $ \env -> do
    (ta, env1) <- runTc a env
    (tb, env2) <- runTc b env1
    let pa = exprPlace ta
        pb = exprPlace tb
        (parr, sheet0) = freshPlace (tcEnvSheet env2)
    sheet1 <- unify mergeLv pa pb sheet0
    sheet2 <- unify mergeLv parr pa sheet1
    pure (Arr (TcAExpr parr) ta tb, env2 { tcEnvSheet = sheet2 })

-- ----------------------------------------------------------------------
-- Trivial solver: walk the annotated tree, read pinned levels, return a
-- LevelMap.  For v0 this is exactly what 'Lvl' produces directly.
-- ----------------------------------------------------------------------

solveLevels :: TcResult 'SProg -> Either LvErr LevelMap
solveLevels (TcResult (Prog _ ds) sheet) = do
  pairs <- collectNames ds
  resolved <- traverse (resolveOne sheet) pairs
  pure (Map.fromList resolved)

collectNames :: [Tree TcAnn 'SDecl] -> Either LvErr [(Name, Place)]
collectNames = fmap concat . traverse go
  where
    go :: Tree TcAnn 'SDecl -> Either LvErr [(Name, Place)]
    go (CtorDecl (TcADecl p) n _)    = Right [(n, p)]
    go (DataDecl (TcADecl p) n _ ds) = do
      rest <- collectNames ds
      pure ((n, p) : rest)

resolveOne :: Sheet Lv -> (Name, Place) -> Either LvErr (Name, Lv)
resolveOne sheet (n, p) = case fst (levelOf p sheet) of
  Just lv -> Right (n, lv)
  Nothing -> Left UnpinnedLevel
