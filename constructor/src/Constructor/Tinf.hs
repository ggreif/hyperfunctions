{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

-- | First-cut A-side type inference: a 'Lang' carrier that elaborates
--   each 'SExpr' to its 'TyExpr'.
--
--   v0_polyType + path-combining scope (this commit):
--     * Builds structural 'TyExpr' values from the surface grammar
--       (var → 'TyCon', tyParamRef → 'TyVar' with binder path, arr
--       → 'TyArr', app → 'TyApp', star → 'TyUniv').
--     * Type-parameter references are pre-resolved by the parser: it
--       emits 'tyParamRef ann name binderPath' for each occurrence,
--       carrying the defining 'data Foo a' parameter's path.  Two
--       distinct 'a' parameters from different declarations are
--       therefore distinguishable here (the Stern-Gerlach reading).
--     * 'var' is now reserved for nullary type-constructor references;
--       unresolved names produce 'TyUnbound'.
--     * No Robinson unification yet — paths only carry identity into
--       the elaborated 'TyExpr'; unification across uses is future
--       work.
--     * Forall / starVar are universe-layer constructs handled by the
--       level carriers, but here they produce 'TyUniv' stubs (since
--       a '∀l. *l' /is/ a type expression at universe level).
--
--   Carriers like 'Lvl' / 'Tc' / 'HypLinf' continue to compute /levels/
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
import Constructor.Path (Path)
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
  , tinfCtors      :: !(Map Name TyExpr)
    -- ^ Declared constructor names → their types.
  } deriving Show

emptyTinfEnv :: TinfEnv
emptyTinfEnv = TinfEnv Map.empty Map.empty

data TyErr
  = TyUnbound Name
  | TyDuplicateType Name
  | TyDuplicateCtor Name
  | TyMismatch TyExpr TyExpr
    -- ^ Robinson-style unification failure: two types with
    --   incompatible structural heads.  Produced by
    --   "Constructor.TyProc".'meet'; not yet produced by 'Tinf'
    --   directly (the A-side has no unification customer).
  | TyUnresolvedMeta !Path !Path
    -- ^ A metavariable (binder-path × use-path) survived to the
    --   materialisation phase without being bound.  Caller error —
    --   the substitution either didn't see the relevant 'meet' or
    --   the carrier failed to drive unification to completion.
  | TyArityMismatch !Name !Int !Int
    -- ^ @TyArityMismatch tycon arity supplied@.  A parametric tycon
    --   received the wrong number of arguments at a use site.
  | TyOccursCheck !Path !Path
    -- ^ Structural occurs check: would-be binding @m := v@ where @v@
    --   contains @m@ transitively (through 'Subst' chasing and
    --   recursion into 'TyAppV' / 'TyArrV' children).  'MetaId'
    --   inlined as its (binder-path, use-path) pair so 'TyErr' has
    --   no dependency on 'Constructor.TyProc'.
  | TyTowerOccurs !Path !Path
    -- ^ Tower-aware occurs check: would-be binding @m := v@ where
    --   the upward tower of @v@ (regenerated under the prospective
    --   substitution) contains @m@ at some rung — i.e., binding
    --   @m@ would make some kind annotation in the typing tower
    --   transitively refer back to @m@.  Catches the Weird-via-meta
    --   shape that pure structural occurs misses (the meta is
    --   horizontally absent at rung 0 but vertically reachable via
    --   'kindOf').
  | TyCtorBadResult !Name
    -- ^ A constructor's annotation peels (under arrows) to a result
    --   type that isn't headed by any type-constructor.  E.g.,
    --   @c : T -> a@ where @a@ is a parameter (so the result is
    --   a 'TyVarV'), or @c : T -> *0@ (the result is 'TyUnivV').
    --   The shape doesn't identify which data the ctor belongs to.
  | TyCtorWrongHead !Name !Name !Name
    -- ^ @TyCtorWrongHead ctor expectedParent actualHead@.  A ctor
    --   inside @data D ...@ has a result headed by a different
    --   tycon (e.g., @c : T -> Bool@ inside @data D@).  Enforced
    --   only when @D@ has arity ≥ 1; for nullary parents the
    --   singleton-family pattern (Swap-style: @Left : Right@) is
    --   accepted by relaxation.
  | TyCtorWrongArity !Name !Name !Int !Int
    -- ^ @TyCtorWrongArity ctor parent expected supplied@.  A ctor
    --   inside @data D (p1 : K1) ... (pn : Kn)@ has result @D@
    --   applied to a wrong number of arguments — e.g., @c : T ->
    --   D@ inside @data D (a : *0)@ (expected 1, supplied 0).
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

  dataDecl _ann _declPath name params _e ds = Tinf $ \env -> do
    -- Register the new data type; reject duplicates.  Parameter scope
    -- is handled in the parser (which resolves each occurrence to a
    -- 'tyParamRef' with binder path), so no scope threading here.
    case Map.lookup name (tinfDataTypes env) of
      Just _  -> Left (TyDuplicateType name)
      Nothing -> do
        let env1 = env
              { tinfDataTypes = Map.insert name (length params) (tinfDataTypes env) }
        env2 <- threadDecls ds env1
        pure (TyVDecl Nothing, env2)

  ctorDecl _ann name e = Tinf $ \env -> do
    (val, env1) <- runTinf e env
    let ty = tyExprOf val
    case Map.lookup name (tinfCtors env1) of
      Just _  -> Left (TyDuplicateCtor name)
      Nothing ->
        let env2 = env1 { tinfCtors = Map.insert name ty (tinfCtors env1) }
        in Right (TyVDecl (Just (name, ty)), env2)

  -- The parser now resolves all type-constructor references via
  -- 'tyConRef'; 'var' is reached only for genuinely unbound names.
  var _ann n = Tinf $ \_env -> Left (TyUnbound n)

  tyConRef _ann n path = Tinf $ \env ->
    Right (TyVExpr (TyCon n path), env)

  tyParamRef _ann n path = Tinf $ \env ->
    Right (TyVExpr (TyVar n path), env)

  star _ann w = Tinf $ \env ->
    Right (TyVExpr (TyUniv (starLevel w)), env)

  arr _ann a b = Tinf $ \env -> do
    (va, env1) <- runTinf a env
    (vb, env2) <- runTinf b env1
    pure (TyVExpr (TyArr (tyExprOf va) (tyExprOf vb)), env2)

  -- A side does not yet perform parametric instantiation, so the
  -- application path is ignored at this layer.
  app _ann _path f x = Tinf $ \env -> do
    (vf, env1) <- runTinf f env
    (vx, env2) <- runTinf x env1
    pure (TyVExpr (TyApp (tyExprOf vf) (tyExprOf vx)), env2)

  -- Level-binder constructs.  We treat the polymorphic universe as a
  -- 'TyUniv' tag — universe polymorphism interacts with this layer
  -- minimally for v0_polyType.
  forallLv _ann _name _path body = Tinf $ runTinf body
  existsTy _ann _name _path body = Tinf $ runTinf body

  -- @*(l + n)@ as a value-level type expression doesn't strictly fit
  -- the value-type universe — but for symmetry we tag it as a
  -- universe at level @S^n (LVar p)@.
  starVar _ann _name _path _offset = Tinf $ \env ->
    Right (TyVExpr (TyUniv Z), env)   -- placeholder: full level fidelity later
