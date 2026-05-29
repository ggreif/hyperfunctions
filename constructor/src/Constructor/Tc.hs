{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}

-- | Constraint generation as a separate Lang HKT pass.
--
--   The carrier 'Tc' builds, for each subterm, a 'TcVal' that pairs a
--   'Place' on the substrate with the subterm's 'Tree' representation.
--   The 'Lang' instance reads neighbours' 'Place's via the 'TcVal' field
--   accessor — it never pattern-matches on 'Tree' itself.  Tree-walking
--   (the genuinely non-compositional analysis: name collection,
--   substitution, error reporting) is the solver's job, and lives in
--   'solveLevels' below.
--
--   The Tree is still built — via the lowercase 'Lang' vocabulary at
--   'r ~ Tree' — but it is opaque to the 'Tc' instance itself.  That
--   restores the finally-tagless discipline inside the algebra: the
--   instance only *constructs*; only the post-pass *inspects*.
module Constructor.Tc
  ( TcAnn (..)
  , TcVal (..)
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

-- | Per-sort annotation on the built 'Tree'.  'SExpr' nodes carry their
--   substrate 'Place'; 'SDecl' carries the declared name's place.
data TcAnn (s :: Sort) where
  TcAExpr :: !Place -> TcAnn 'SExpr
  TcADecl :: !Place -> TcAnn 'SDecl
  TcAProg :: TcAnn 'SProg

deriving instance Show (TcAnn s)
deriving instance Eq (TcAnn s)

-- | The carrier value: a 'Place' (where exposed) plus the syntactic Tree
--   built so far.  The 'Place' field lets the 'Lang' instance read its
--   children's places by direct projection — no Tree pattern match
--   needed in the algebra.
data TcVal (s :: Sort) where
  TcVExpr :: !Place -> !(Tree TcAnn 'SExpr) -> TcVal 'SExpr
  TcVDecl :: !Place -> !(Tree TcAnn 'SDecl) -> TcVal 'SDecl
  TcVProg ::           !(Tree TcAnn 'SProg) -> TcVal 'SProg

-- Project the 'Place' out of an 'SExpr' carrier value.
tcExprPlace :: TcVal 'SExpr -> Place
tcExprPlace (TcVExpr p _) = p

-- Project the inner 'Tree' so we can pass it to the lowercase Lang
-- methods when assembling parent nodes.
tcValTree :: TcVal s -> Tree TcAnn s
tcValTree = \case
  TcVExpr _ t -> t
  TcVDecl _ t -> t
  TcVProg   t -> t

data TcEnv = TcEnv
  { tcEnvSheet  :: !(Sheet Lv)
  , tcEnvNames  :: !(Map Name Place)
  , tcEnvParent :: !(Maybe Place)
  } deriving Show

emptyTcEnv :: TcEnv
emptyTcEnv = TcEnv emptySheet Map.empty Nothing

-- | Final output: annotated Tree + the Sheet that holds the resolved
--   constraints.
data TcResult (s :: Sort) = TcResult
  { tcResultTree  :: Tree TcAnn s
  , tcResultSheet :: Sheet Lv
  }

-- | The constraint-generation carrier.  Phantom in @a@.
newtype Tc (a :: Sort -> Type) (s :: Sort) = Tc
  { runTc :: TcEnv -> Either LvErr (TcVal s, TcEnv) }

-- | Top-level entry: @parseProgram \@Tc@ then 'tcProgram'.
tcProgram :: Tc a 'SProg -> Either LvErr (TcResult 'SProg)
tcProgram p = do
  (val, env) <- runTc p emptyTcEnv
  case val of
    TcVProg tree -> pure (TcResult tree (tcEnvSheet env))

-- ----------------------------------------------------------------------
-- The Lang instance.
--
-- Build phase: every constructor goes through the lowercase Lang
-- vocabulary at 'r ~ Tree'.  The instance never patterns-matches on
-- 'Tree' — 'Place' reads come through 'tcExprPlace'.
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
  -> Either LvErr ([TcVal 'SDecl], TcEnv)
threadDecls []     env = Right ([], env)
threadDecls (d:ds) env = do
  (v,  env1) <- runTc d env
  (vs, env2) <- threadDecls ds env1
  pure (v : vs, env2)

instance Lang Tc where
  prog _ann ds = Tc $ \env -> do
    (vs, env') <- threadDecls ds env
    let tree :: Tree TcAnn 'SProg
        tree = prog TcAProg (map tcValTree vs)
    pure (TcVProg tree, env')

  dataDecl _ann n e ds = Tc $ \env -> do
    (ev, env1) <- runTc e env
    let pe = tcExprPlace ev
        (mLe, sheet1) = levelOf pe (tcEnvSheet env1)
        env1' = env1 { tcEnvSheet = sheet1 }
    le <- maybe (Left UnpinnedLevel) Right mLe
    ln <- maybe (Left (DataAnnotationTooLow n le)) Right (predLv le)
    let (pn, sheet2) = freshPlace (tcEnvSheet env1')
    sheet3 <- pin mergeLv pn ln sheet2
    env2  <- bind n pn (env1' { tcEnvSheet = sheet3, tcEnvParent = Just pn })
    (vs, env3) <- threadDecls ds env2
    let tree :: Tree TcAnn 'SDecl
        tree = dataDecl (TcADecl pn) n (tcValTree ev) (map tcValTree vs)
    pure (TcVDecl pn tree, env3 { tcEnvParent = tcEnvParent env1' })

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
    let tree :: Tree TcAnn 'SDecl
        tree = ctorDecl (TcADecl pc) n (tcValTree tv)
    pure (TcVDecl pc tree, env2)

  var _ann x = Tc $ \env -> case Map.lookup x (tcEnvNames env) of
    Just p  -> let tree :: Tree TcAnn 'SExpr
                   tree = var (TcAExpr p) x
               in Right (TcVExpr p tree, env)
    Nothing -> Left (Unbound x)

  star _ann w = Tc $ \env -> do
    let (p, sheet1) = freshPlace (tcEnvSheet env)
    sheet2 <- pin mergeLv p (starLevel w) sheet1
    let tree :: Tree TcAnn 'SExpr
        tree = star (TcAExpr p) w
    pure (TcVExpr p tree, env { tcEnvSheet = sheet2 })

  arr _ann a b = Tc $ \env -> do
    (av, env1) <- runTc a env
    (bv, env2) <- runTc b env1
    let pa = tcExprPlace av
        pb = tcExprPlace bv
        (parr, sheet0) = freshPlace (tcEnvSheet env2)
    sheet1 <- unify mergeLv pa pb sheet0
    sheet2 <- unify mergeLv parr pa sheet1
    let tree :: Tree TcAnn 'SExpr
        tree = arr (TcAExpr parr) (tcValTree av) (tcValTree bv)
    pure (TcVExpr parr tree, env2 { tcEnvSheet = sheet2 })

-- ----------------------------------------------------------------------
-- Solver: a legitimate deep tree-walk, allowed to pattern-match on the
-- Tree's constructors.  Reads Places from the Tree's annotations,
-- resolves them against the Sheet, returns a LevelMap.
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
