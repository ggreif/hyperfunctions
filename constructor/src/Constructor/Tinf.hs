{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

-- | First-cut A-side type inference: a 'Lang' carrier that elaborates
--   each 'SExpr' to its 'TyExpr'.
--
--   v0_polyType scope (this commit):
--     * Validates identifier references (data type names + in-scope
--       type parameters).
--     * Builds structural 'TyExpr' values from the surface grammar
--       (var → 'TyVar' / 'TyCon', arr → 'TyArr', app → 'TyApp',
--       star → 'TyUniv').
--     * No Robinson unification yet — same-named type variables share
--       identity by name within a data declaration's scope; cross-
--       declaration unification is future work.
--     * Forall / starVar are universe-layer constructs handled by the
--       level carriers, but here they produce 'TyUniv' stubs (since
--       a '∀l. *l' /is/ a type expression at universe level).
--
--   Carriers like 'Lvl' / 'Tc' / 'HypTc' continue to compute /levels/
--   independently; 'Tinf' computes /types/.  A future carrier will
--   combine them (level + type in one pass) when both are needed
--   simultaneously.
module Constructor.Tinf
  ( Tinf
  , TyVal (..)
  , TyErr (..)
  , TyResult (..)
  , tinfProgram
  ) where

import Constructor.Level (Lv (..), starLevel)
import Constructor.Sort (Sort (..))
import Constructor.Syntax (Lang (..), Name)
import Constructor.TyExpr (TyExpr (..))
import Data.Kind (Type)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

-- | Per-sort carrier value.
data TyVal (s :: Sort) where
  TyVExpr :: !TyExpr -> TyVal 'SExpr
  TyVDecl :: !(Maybe (Name, TyExpr)) -> TyVal 'SDecl
    -- ^ For a 'ctorDecl', @Just (ctorName, ctorTy)@; for 'dataDecl', 'Nothing'.
  TyVProg :: TyVal 'SProg

-- | Environment threaded through inference.
data TinfEnv = TinfEnv
  { tinfDataTypes  :: !(Map Name Int)
    -- ^ Declared data type names → their arity.
  , tinfParamScope :: !(Map Name ())
    -- ^ In-scope type parameters of the enclosing data declaration.
    --   Value is '()' because identity is by name for this commit.
  , tinfCtors      :: !(Map Name TyExpr)
    -- ^ Declared constructor names → their types.
  } deriving Show

emptyTinfEnv :: TinfEnv
emptyTinfEnv = TinfEnv Map.empty Map.empty Map.empty

data TyErr
  = TyUnbound Name
  | TyDuplicateType Name
  | TyDuplicateCtor Name
  deriving (Eq, Show)

data TyResult = TyResult
  { tyResultDataTypes :: !(Map Name Int)
  , tyResultCtors     :: !(Map Name TyExpr)
  } deriving Show

-- | The type-inference carrier.  Phantom in the user-supplied annotation.
newtype Tinf (a :: Sort -> Type) (s :: Sort) = Tinf
  { runTinf :: TinfEnv -> Either TyErr (TyVal s, TinfEnv) }

tinfProgram :: Tinf a 'SProg -> Either TyErr TyResult
tinfProgram p = do
  (_, env) <- runTinf p emptyTinfEnv
  pure (TyResult (tinfDataTypes env) (tinfCtors env))

-- | Project the 'TyExpr' out of an 'SExpr' carrier value.
tyExprOf :: TyVal 'SExpr -> TyExpr
tyExprOf (TyVExpr t) = t

threadDecls :: [Tinf a 'SDecl] -> TinfEnv -> Either TyErr TinfEnv
threadDecls []     env = Right env
threadDecls (d:ds) env = do
  (_, env1) <- runTinf d env
  threadDecls ds env1

instance Lang Tinf where
  prog _ann ds = Tinf $ \env -> do
    env' <- threadDecls ds env
    pure (TyVProg, env')

  dataDecl _ann name params _e ds = Tinf $ \env -> do
    -- Register the new data type; reject duplicates.
    case Map.lookup name (tinfDataTypes env) of
      Just _  -> Left (TyDuplicateType name)
      Nothing -> do
        let env1 = env
              { tinfDataTypes  = Map.insert name (length params) (tinfDataTypes env)
                -- Bring parameters into scope for the body.
              , tinfParamScope = foldr (`Map.insert` ()) (tinfParamScope env) params
              }
        env2 <- threadDecls ds env1
        -- Restore parameter scope after body (the data's params don't
        -- leak to sibling declarations).
        pure (TyVDecl Nothing, env2 { tinfParamScope = tinfParamScope env })

  ctorDecl _ann name e = Tinf $ \env -> do
    (val, env1) <- runTinf e env
    let ty = tyExprOf val
    case Map.lookup name (tinfCtors env1) of
      Just _  -> Left (TyDuplicateCtor name)
      Nothing ->
        let env2 = env1 { tinfCtors = Map.insert name ty (tinfCtors env1) }
        in Right (TyVDecl (Just (name, ty)), env2)

  var _ann n = Tinf $ \env ->
    case Map.lookup n (tinfParamScope env) of
      Just () -> Right (TyVExpr (TyVar n), env)
      Nothing -> case Map.lookup n (tinfDataTypes env) of
        Just _  -> Right (TyVExpr (TyCon n), env)
        Nothing -> Left (TyUnbound n)

  star _ann w = Tinf $ \env ->
    Right (TyVExpr (TyUniv (starLevel w)), env)

  arr _ann a b = Tinf $ \env -> do
    (va, env1) <- runTinf a env
    (vb, env2) <- runTinf b env1
    pure (TyVExpr (TyArr (tyExprOf va) (tyExprOf vb)), env2)

  app _ann f x = Tinf $ \env -> do
    (vf, env1) <- runTinf f env
    (vx, env2) <- runTinf x env1
    pure (TyVExpr (TyApp (tyExprOf vf) (tyExprOf vx)), env2)

  -- Level-binder constructs.  We treat the polymorphic universe as a
  -- 'TyUniv' tag — universe polymorphism interacts with this layer
  -- minimally for v0_polyType.
  forallLv _ann _name _path body = Tinf $ runTinf body

  -- @*(l + n)@ as a value-level type expression doesn't strictly fit
  -- the value-type universe — but for symmetry we tag it as a
  -- universe at level @S^n (LVar p)@.
  starVar _ann _name _path _offset = Tinf $ \env ->
    Right (TyVExpr (TyUniv Z), env)   -- placeholder: full level fidelity later
