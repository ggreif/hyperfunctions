{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Architecture B: hyperfunction-driven carrier.  Parallel sibling to
--   'Constructor.Tc' (Architecture A, Sheet-driven).
--
--   The 'Sheet' substrate is replaced by a web of 'Hyper'-valued
--   type-processes.  Each place in the web IS a hyperfunction; two
--   places are "identified" when their self-applications yield
--   compatible values.  For v0 (flat levels, no inference variables)
--   the web is shallow — every type-process is 'hPure n' — so the
--   architectural difference doesn't show up in expressive power.
--   It earns its keep when type-inference variables arrive and the
--   path-tracing character of hyperfunction self-application starts
--   carrying real information (the witness of each identification).
--
--   The carrier is impredicative in the same shape as 'Constructor.Tc':
--   each method emits the analysis result and a polymorphic
--   finally-tagless term decorated by inferred levels in one go.
module Constructor.HypTc
  ( HypVal (..)
  , HypResult (..)
  , HypTc
  , hypProgram
  , hypRunWith
  , solveLevelsHyp
  ) where

import Constructor.HyperLite (Hyper, hPure, hRun)
import Constructor.Level (Lv (..), starLevel)
import Constructor.LevelInfer (LevelMap, LvErr (..))
import Constructor.Sort (Sort (..))
import Constructor.Syntax (Lang (..), Name)
import Constructor.Tc (Discard, LvAnnot (..))
import Data.Kind (Type)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

-- | A type-process: a hyperfunction that, when self-applied, yields
--   the level of the place it represents.
type LvProc = Hyper Lv Lv

-- | Carrier value.  No 'Place' tag — the hyperfunction itself IS the
--   place; identifications happen via self-application, not via
--   union-find roots.
data HypVal (s :: Sort) where
  HypVExpr :: !LvProc -> HypVal 'SExpr
  HypVDecl :: !LvProc -> HypVal 'SDecl
  HypVProg ::            HypVal 'SProg

hypExprProc :: HypVal 'SExpr -> LvProc
hypExprProc (HypVExpr p) = p

data HypEnv = HypEnv
  { hypEnvNames  :: !(Map Name LvProc)
  , hypEnvParent :: !(Maybe LvProc)
  }

emptyHypEnv :: HypEnv
emptyHypEnv = HypEnv Map.empty Nothing

-- | Solver-facing analysis result.  Just the bound-name → type-process
--   map; no Sheet to consult.  Levels are obtained by self-applying
--   each process via 'hRun'.
data HypResult = HypResult
  { hypResultNames :: !(Map Name LvProc)
  }

-- | The hyperfunction-driven carrier.  Phantom in @a@; impredicative
--   third tuple slot for the polymorphic LvAnnot-decorated term.
newtype HypTc (a :: Sort -> Type) (s :: Sort) = HypTc
  { runHypTc :: forall r. Lang r =>
                HypEnv -> Either LvErr (HypVal s, HypEnv, r LvAnnot s)
  }

-- | Analysis only (specialises the polymorphic slot at 'Discard').
hypProgram :: HypTc a 'SProg -> Either LvErr HypResult
hypProgram p = do
  (_, env, _ :: Discard LvAnnot 'SProg) <- runHypTc p emptyHypEnv
  pure (HypResult (hypEnvNames env))

-- | Analysis + polymorphic LvAnnot term at the caller's chosen @r@.
hypRunWith
  :: forall r a. Lang r
  => HypTc a 'SProg
  -> Either LvErr (HypResult, r LvAnnot 'SProg)
hypRunWith p = do
  (_, env, term) <- runHypTc p emptyHypEnv
  pure (HypResult (hypEnvNames env), term)

-- ----------------------------------------------------------------------
-- The Lang instance.  Compatibility-of-places becomes "their
-- self-applications agree" — direct semantic check via 'hRun', no
-- union-find machinery.
-- ----------------------------------------------------------------------

predLv :: Lv -> Maybe Lv
predLv Z     = Nothing
predLv (S n) = Just n

bind :: Name -> LvProc -> HypEnv -> Either LvErr HypEnv
bind n p env
  | Map.member n (hypEnvNames env) = Left (Duplicate n)
  | otherwise = Right env { hypEnvNames = Map.insert n p (hypEnvNames env) }

threadDecls
  :: forall r a. Lang r
  => [HypTc a 'SDecl]
  -> HypEnv
  -> Either LvErr ([r LvAnnot 'SDecl], HypEnv)
threadDecls []     env = Right ([], env)
threadDecls (d:ds) env = do
  (_, env1, t)  <- runHypTc d env
  (ts, env2)    <- threadDecls ds env1
  pure (t : ts, env2)

instance Lang HypTc where
  prog _ann ds = HypTc $ \env -> do
    (ts, env') <- threadDecls ds env
    pure (HypVProg, env', prog LvAProg ts)

  dataDecl _ann n e ds = HypTc $ \env -> do
    (ev, env1, polyE) <- runHypTc e env
    let procE = hypExprProc ev
        le    = hRun procE
    ln <- maybe (Left (DataAnnotationTooLow n le)) Right (predLv le)
    let procN = hPure ln
    env2 <- bind n procN (env1 { hypEnvParent = Just procN })
    (polys, env3) <- threadDecls ds env2
    pure ( HypVDecl procN
         , env3 { hypEnvParent = hypEnvParent env1 }
         , dataDecl (LvADecl ln) n polyE polys
         )

  ctorDecl _ann n t = HypTc $ \env -> do
    parent <- maybe (Left (CtorOutsideData n)) Right (hypEnvParent env)
    (tv, env1, polyT) <- runHypTc t env
    let procT = hypExprProc tv
        lt    = hRun procT
        lp    = hRun parent
    if lt /= lp
      then Left (LevelTear lt lp)
      else do
        lc <- maybe (Left (DataAnnotationTooLow n lp)) Right (predLv lp)
        let procC = hPure lc
        env2 <- bind n procC env1
        pure (HypVDecl procC, env2, ctorDecl (LvADecl lc) n polyT)

  var _ann x = HypTc $ \env -> case Map.lookup x (hypEnvNames env) of
    Just proc ->
      let lv = hRun proc
      in Right (HypVExpr proc, env, var (LvAExpr lv) x)
    Nothing -> Left (Unbound x)

  star _ann w = HypTc $ \env -> do
    let lv   = starLevel w
        proc = hPure lv
    pure (HypVExpr proc, env, star (LvAExpr lv) w)

  arr _ann a b = HypTc $ \env -> do
    (av, env1, polyA) <- runHypTc a env
    (bv, env2, polyB) <- runHypTc b env1
    let procA = hypExprProc av
        procB = hypExprProc bv
        lvA   = hRun procA
        lvB   = hRun procB
    if lvA /= lvB
      then Left (LevelTear lvA lvB)
      else
        -- Same level: both processes inhabit the same fibre of the cover;
        -- reuse one as the arrow's process.  In the path-tracking
        -- (groupoid) reading, this is the trivial identification —
        -- the path from procA to procB is the no-op.
        let lv = lvA
        in Right (HypVExpr procA, env2, arr (LvAExpr lv) polyA polyB)

-- ----------------------------------------------------------------------
-- Solver: invoke each name's hyperfunction to extract its level.
-- ----------------------------------------------------------------------

solveLevelsHyp :: HypResult -> Either LvErr LevelMap
solveLevelsHyp r = Right (Map.map hRun (hypResultNames r))
