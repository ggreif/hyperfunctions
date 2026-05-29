{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

-- | Architecture B's type-inference carrier — direct sibling of
--   'Constructor.Tinf'.
--
--   Where 'Tinf' threads a state-monadic environment and produces
--   syntactic 'TyExpr' values, 'HypTinf' parks each elaborated type
--   as a 'TyProc' web ('Constructor.TyProc').  Extraction back to
--   syntax happens via 'procToTy', which is the dual unfolder of
--   'tyToProc' — the "probe" extraction the design notes converged
--   on, with no shadow-state representation kept on the side.
--
--   For commit 4 the algebra adds no expressive power over 'Tinf':
--   every 'TyProc' is the trivial @hPure view@ of a fully-known
--   type, and the parity tests in 'TinfSpec' / 'HypTinfSpec'
--   confirm A and B agree on the current corpus.  The carrier
--   shape — including the metavariable parking slot 'TyMetaV' —
--   is in place so commit 5's unifier can land without reshaping
--   the algebra.
module Constructor.HypTinf
  ( HypTinf
  , HypTinfVal (..)
  , HypTinfResult (..)
  , hypTinfProgram
  , hypTinfCtorTypes
  ) where

import Constructor.HyperLite (hPure, hRun)
import Constructor.Level (Lv (..), starLevel)
import Constructor.Path (Path, PathStep (..), extendPath)
import Constructor.Sort (Sort (..))
import Constructor.Syntax (Lang (..), Name)
import Constructor.TyExpr (TyExpr)
import Constructor.TyProc
  ( Subst
  , TyProc
  , TyView (..)
  , emptySubst
  , materialize
  , meet
  , mkMeta
  )
import Constructor.Tinf (TyErr (..))
import Data.Kind (Type)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

-- | Per-sort carrier value.  An 'SExpr' is a type-process; an
--   'SDecl' carries the constructor's (name, process) pair if it is
--   a constructor declaration (data declarations emit 'Nothing').
data HypTinfVal (s :: Sort) where
  HypTinfExpr :: !TyProc                       -> HypTinfVal 'SExpr
  HypTinfDecl :: !(Maybe (Name, TyProc))       -> HypTinfVal 'SDecl
  HypTinfProg ::                                  HypTinfVal 'SProg

-- | No 'Show' — 'TyProc' / 'Subst' contain function values.
data HypTinfEnv = HypTinfEnv
  { hypEnvDataTypes :: !(Map Name Int)
  , hypEnvCtors     :: !(Map Name TyProc)
  , hypEnvSubst     :: !Subst
  }

emptyHypTinfEnv :: HypTinfEnv
emptyHypTinfEnv = HypTinfEnv Map.empty Map.empty emptySubst

data HypTinfResult = HypTinfResult
  { hypTinfDataTypes :: !(Map Name Int)
  , hypTinfCtors     :: !(Map Name TyProc)
  , hypTinfSubst     :: !Subst
  }

-- | Extract a 'Map Name TyExpr' from a 'HypTinfResult' by
--   materialising each constructor's type-process under the result's
--   substitution.  The B-side analog of @tyResultCtors@.  Returns
--   'Left' if any ctor's process retained an unresolved meta — for
--   well-formed input that only happens if commit-6's parametric
--   instantiation didn't fully constrain the metas (occurs check or
--   missing customer).
hypTinfCtorTypes :: HypTinfResult -> Either TyErr (Map Name TyExpr)
hypTinfCtorTypes r = traverse (materialize (hypTinfSubst r)) (hypTinfCtors r)

-- | The type-inference carrier.  Phantom in the user-supplied annotation.
newtype HypTinf (a :: Sort -> Type) (s :: Sort) = HypTinf
  { runHypTinf :: HypTinfEnv -> Either TyErr (HypTinfVal s, HypTinfEnv) }

hypTinfProgram :: HypTinf a 'SProg -> Either TyErr HypTinfResult
hypTinfProgram p = do
  (_, env) <- runHypTinf p emptyHypTinfEnv
  pure (HypTinfResult (hypEnvDataTypes env) (hypEnvCtors env) (hypEnvSubst env))

-- | Project the 'TyProc' out of an 'SExpr' carrier value.
exprProc :: HypTinfVal 'SExpr -> TyProc
exprProc (HypTinfExpr p) = p

threadDecls :: [HypTinf a 'SDecl] -> HypTinfEnv -> Either TyErr HypTinfEnv
threadDecls []     env = Right env
threadDecls (d:ds) env = do
  (_, env1) <- runHypTinf d env
  threadDecls ds env1

-- | Walk the function-position spine of an application, returning
--   the eventual tycon head (its name + decl-path) and how many
--   arguments have already been consumed before this app step.
--   Yields 'Nothing' for the head if the spine doesn't bottom out
--   in a 'TyConV' (e.g. a free var or future grammar feature).
spineHead :: TyProc -> (Maybe (Name, Path), Int)
spineHead p = go (hRun p) 0
  where
    go (TyConV n declP) depth = (Just (n, declP), depth)
    go (TyAppV g _)     depth = go (hRun g) (depth + 1)
    go _                _     = (Nothing, 0)

-- | Allocate the meta for the next parameter of a parametric tycon
--   and unify it with the argument.  No-op for non-tycon heads (the
--   carrier just constructs 'TyAppV'); 'TyArityMismatch' if the
--   spine has already consumed all of the tycon's parameters.
instantiateOne
  :: Path -> TyProc -> TyProc -> HypTinfEnv -> Either TyErr HypTinfEnv
instantiateOne appPath procF procX env = case spineHead procF of
  (Just (name, declP), depth) -> case Map.lookup name (hypEnvDataTypes env) of
    Just arity
      | depth >= arity -> Left (TyArityMismatch name arity (depth + 1))
      | otherwise ->
          let metaBinderPath = extendPath (PsDataParam depth) declP
              metaProc       = mkMeta metaBinderPath appPath
          in do
            subst' <- meet (hypEnvSubst env) metaProc procX
            Right env { hypEnvSubst = subst' }
    Nothing -> Right env  -- parser already validated the tycon exists
  (Nothing, _) -> Right env

instance Lang HypTinf where
  prog _ann ds = HypTinf $ \env -> do
    env' <- threadDecls ds env
    pure (HypTinfProg, env')

  dataDecl _ann name params _e ds = HypTinf $ \env ->
    case Map.lookup name (hypEnvDataTypes env) of
      Just _  -> Left (TyDuplicateType name)
      Nothing -> do
        let env1 = env
              { hypEnvDataTypes = Map.insert name (length params) (hypEnvDataTypes env) }
        env2 <- threadDecls ds env1
        pure (HypTinfDecl Nothing, env2)

  ctorDecl _ann name e = HypTinf $ \env -> do
    (val, env1) <- runHypTinf e env
    let proc_ = exprProc val
    case Map.lookup name (hypEnvCtors env1) of
      Just _  -> Left (TyDuplicateCtor name)
      Nothing ->
        let env2 = env1 { hypEnvCtors = Map.insert name proc_ (hypEnvCtors env1) }
        in Right (HypTinfDecl (Just (name, proc_)), env2)

  -- Parser owns type-constructor resolution; 'var' is only reached
  -- for genuinely unbound names.
  var _ann n = HypTinf $ \_env -> Left (TyUnbound n)

  tyConRef _ann n path = HypTinf $ \env ->
    Right (HypTinfExpr (hPure (TyConV n path)), env)

  tyParamRef _ann n path = HypTinf $ \env ->
    Right (HypTinfExpr (hPure (TyVarV n path)), env)

  star _ann w = HypTinf $ \env ->
    Right (HypTinfExpr (hPure (TyUnivV (starLevel w))), env)

  -- Children stay as TyProcs — the type is a web of hyperfunctions,
  -- not a tree of TyExprs.  hPure here parks the one-layer view; the
  -- children negotiate at extraction or unification time.
  arr _ann a b = HypTinf $ \env -> do
    (va, env1) <- runHypTinf a env
    (vb, env2) <- runHypTinf b env1
    pure (HypTinfExpr (hPure (TyArrV (exprProc va) (exprProc vb))), env2)

  -- Parametric instantiation customer for 'meet': inspect the
  -- function spine — if it terminates in a parametric tycon, allocate
  -- a fresh metavariable addressed by (parameter-binder-path, this
  -- application's path) and unify it with the supplied argument.
  -- The resulting Subst extension records what each parameter at
  -- each use site has been bound to.  Non-tycon heads (e.g. an
  -- unresolved free variable in a future grammar feature) flow
  -- through untouched.
  app _ann appPath f x = HypTinf $ \env -> do
    (vf, env1) <- runHypTinf f env
    (vx, env2) <- runHypTinf x env1
    let procF = exprProc vf
        procX = exprProc vx
    env3 <- instantiateOne appPath procF procX env2
    pure (HypTinfExpr (hPure (TyAppV procF procX)), env3)

  forallLv _ann _name _path body = HypTinf $ runHypTinf body

  starVar _ann _name _path _offset = HypTinf $ \env ->
    Right (HypTinfExpr (hPure (TyUnivV Z)), env)
