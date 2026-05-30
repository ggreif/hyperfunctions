{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Architecture B: hyperfunction-driven level-inference carrier.
--   Parallel sibling to 'Constructor.Tc' (Architecture A, Sheet-driven
--   level inference).
--
--   The 'Sheet' substrate is replaced by a web of 'Hyper'-valued
--   level-processes.  Each place in the web IS a hyperfunction; two
--   places are "identified" when their self-applications yield
--   compatible values.  For v0 (flat levels, no inference variables)
--   the web is shallow — every level-process is 'hPure n' — so the
--   architectural difference doesn't show up in expressive power.
--   It earns its keep when level-inference variables arrive and the
--   path-tracing character of hyperfunction self-application starts
--   carrying real information (the witness of each identification).
--
--   The carrier is impredicative in the same shape as 'Constructor.Tc':
--   each method emits the analysis result and a polymorphic
--   finally-tagless term decorated by inferred levels in one go.
--   That polymorphic third slot is what 'Constructor.HypTinf' (B-side
--   type inference) consumes — specialise at @r ~ HypTinf@ via
--   'hypLinfRunWith' and the level annotations flow into type
--   inference as input.
module Constructor.HypLinf
  ( HypLinfVal (..)
  , HypLinfResult (..)
  , HypLinf
  , hypLinfProgram
  , hypLinfRunWith
  , solveLevelsHypLinf
  ) where

import Constructor.HyperLite (Hyper, hPure, hRun)
import Constructor.Level (Lv (..), addOffset, starLevel)
import Constructor.LevelInfer (LevelMap, LvErr (..))
import Constructor.Sort (Sort (..))
import Constructor.Syntax (Lang (..), Name)
import Constructor.Tc (Discard, LvAnnot (..))
import Data.Kind (Type)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

-- | A level-process: a hyperfunction that, when self-applied, yields
--   the level of the place it represents.
type LvProc = Hyper Lv Lv

-- | Carrier value.  No 'Place' tag — the hyperfunction itself IS the
--   place; identifications happen via self-application, not via
--   union-find roots.
data HypLinfVal (s :: Sort) where
  HypLinfExpr :: !LvProc -> HypLinfVal 'SExpr
  HypLinfDecl :: !LvProc -> HypLinfVal 'SDecl
  HypLinfProg ::            HypLinfVal 'SProg

hypLinfExprProc :: HypLinfVal 'SExpr -> LvProc
hypLinfExprProc (HypLinfExpr p) = p

data HypLinfEnv = HypLinfEnv
  { hypLinfEnvNames  :: !(Map Name LvProc)
  , hypLinfEnvParent :: !(Maybe LvProc)
  }

emptyHypLinfEnv :: HypLinfEnv
emptyHypLinfEnv = HypLinfEnv Map.empty Nothing

-- | Solver-facing analysis result.  Just the bound-name → level-process
--   map; no Sheet to consult.  Levels are obtained by self-applying
--   each process via 'hRun'.
data HypLinfResult = HypLinfResult
  { hypLinfResultNames :: !(Map Name LvProc)
  }

-- | The hyperfunction-driven level-inference carrier.  Phantom in @a@;
--   impredicative third tuple slot for the polymorphic LvAnnot-
--   decorated term.
newtype HypLinf (a :: Sort -> Type) (s :: Sort) = HypLinf
  { runHypLinf :: forall r. Lang r =>
                  HypLinfEnv -> Either LvErr (HypLinfVal s, HypLinfEnv, r LvAnnot s)
  }

-- | Analysis only (specialises the polymorphic slot at 'Discard').
hypLinfProgram :: HypLinf a 'SProg -> Either LvErr HypLinfResult
hypLinfProgram p = do
  (_, env, _ :: Discard LvAnnot 'SProg) <- runHypLinf p emptyHypLinfEnv
  pure (HypLinfResult (hypLinfEnvNames env))

-- | Analysis + polymorphic LvAnnot term at the caller's chosen @r@.
hypLinfRunWith
  :: forall r a. Lang r
  => HypLinf a 'SProg
  -> Either LvErr (HypLinfResult, r LvAnnot 'SProg)
hypLinfRunWith p = do
  (_, env, term) <- runHypLinf p emptyHypLinfEnv
  pure (HypLinfResult (hypLinfEnvNames env), term)

-- ----------------------------------------------------------------------
-- The Lang instance.  Compatibility-of-places becomes "their
-- self-applications agree" — direct semantic check via 'hRun', no
-- union-find machinery.
-- ----------------------------------------------------------------------

predLv :: Lv -> Maybe Lv
predLv Z        = Nothing
predLv (S n)    = Just n
predLv (LVar p) = Just (LVar p)
  -- ^ A level variable is its own predecessor: at the parametric
  -- level coordinate the @n = predLv n@ equation has 'LVar' as
  -- fixpoint.  This is what makes the stratified @data Weird :
  -- Weird@ shape navigable through the level layer — Weird's
  -- level is universe-polymorphic, fixed at its def-path 'LVar',
  -- and predLv reflects that "the rung above Weird is at the
  -- same level coordinate" (the offset lives in 'TyConV's
  -- deck-shift slot, not in 'Lv').  For @S^k (LVar p)@ inputs
  -- (level-polymorphic with concrete offset), the @S@ rule
  -- strips one layer as usual; the bare-LVar case only fires for
  -- pure self-stratification.

bind :: Name -> LvProc -> HypLinfEnv -> Either LvErr HypLinfEnv
bind n p env
  | Map.member n (hypLinfEnvNames env) = Left (Duplicate n)
  | otherwise = Right env { hypLinfEnvNames = Map.insert n p (hypLinfEnvNames env) }

threadDecls
  :: forall r a. Lang r
  => [HypLinf a 'SDecl]
  -> HypLinfEnv
  -> Either LvErr ([r LvAnnot 'SDecl], HypLinfEnv)
threadDecls []     env = Right ([], env)
threadDecls (d:ds) env = do
  (_, env1, t)  <- runHypLinf d env
  (ts, env2)    <- threadDecls ds env1
  pure (t : ts, env2)

instance Lang HypLinf where
  prog _ann ds = HypLinf $ \env -> do
    (ts, env') <- threadDecls ds env
    pure (HypLinfProg, env', prog LvAProg ts)

  dataDecl _ann declPath n params e ds = HypLinf $ \env -> do
    -- Duplicate check (was the work 'bind' did after elaboration —
    -- now performed up front so the pre-binding can shadow safely
    -- without clobbering an outer same-named decl).
    case Map.lookup n (hypLinfEnvNames env) of
      Just _  -> Left (Duplicate n)
      Nothing -> Right ()
    -- Pre-bind the data name to a tentative 'LVar declPath' before
    -- elaborating the kind annotation.  This makes self-referential
    -- kinds (@data Weird : Weird@) navigable: the inner 'tyConRef'
    -- looks up "Weird" and finds the parametric level, rather than
    -- failing with 'Unbound'.  For non-self-referential decls the
    -- tentative binding is overwritten by the real one below.
    let tentativeProcN = hPure (LVar declPath)
        preEnv = env { hypLinfEnvNames =
                         Map.insert n tentativeProcN (hypLinfEnvNames env) }
    (ev, env1, polyE) <- runHypLinf e preEnv
    let procE = hypLinfExprProc ev
        le    = hRun procE
    ln <- maybe (Left (DataAnnotationTooLow n le)) Right (predLv le)
    let procN = hPure ln
        -- Overwrite the tentative binding with the real one.
        env2 = env1
          { hypLinfEnvNames  = Map.insert n procN (hypLinfEnvNames env1)
          , hypLinfEnvParent = Just procN
          }
    -- Bind each parameter to the data's level for the body's scope.
    -- Save the prior binding for each param name so it doesn't leak
    -- out after the body — different decls reuse the same surface
    -- name ('a' in @data Box a@ and @data Bag a@) without clashing.
    let savedBindings = [(p, Map.lookup p (hypLinfEnvNames env2)) | p <- params]
        paramEnv = env2
          { hypLinfEnvNames =
              Map.union (Map.fromList [(p, procN) | p <- params])
                        (hypLinfEnvNames env2)
          }
    (polys, env3) <- threadDecls ds paramEnv
    let restoredNames =
          foldr (\(p, mOrig) m -> case mOrig of
                   Nothing -> Map.delete p m
                   Just v  -> Map.insert p v m)
                (hypLinfEnvNames env3) savedBindings
    pure ( HypLinfDecl procN
         , env3 { hypLinfEnvParent = hypLinfEnvParent env1
                , hypLinfEnvNames  = restoredNames
                }
         , dataDecl (LvADecl ln) declPath n params polyE polys
         )

  ctorDecl _ann n t = HypLinf $ \env -> do
    parent <- maybe (Left (CtorOutsideData n)) Right (hypLinfEnvParent env)
    (tv, env1, polyT) <- runHypLinf t env
    let procT = hypLinfExprProc tv
        lt    = hRun procT
        lp    = hRun parent
    if lt /= lp
      then Left (LevelTear lt lp)
      else do
        lc <- maybe (Left (DataAnnotationTooLow n lp)) Right (predLv lp)
        let procC = hPure lc
        env2 <- bind n procC env1
        pure (HypLinfDecl procC, env2, ctorDecl (LvADecl lc) n polyT)

  var _ann x = HypLinf $ \env -> case Map.lookup x (hypLinfEnvNames env) of
    Just proc ->
      let lv = hRun proc
      in Right (HypLinfExpr proc, env, var (LvAExpr lv) x)
    Nothing -> Left (Unbound x)

  -- Look the tycon up by name (level inference ignores the def-path
  -- internally — bindings live in 'hypLinfEnvNames'), but the
  -- polymorphic LvAnnot-decorated output preserves the path so
  -- downstream consumers (HypTinf) can route to their own 'tyConRef'
  -- rather than to 'var'.
  tyConRef _ann n path = HypLinf $ \env -> case Map.lookup n (hypLinfEnvNames env) of
    Just proc ->
      let lv = hRun proc
      in Right (HypLinfExpr proc, env, tyConRef (LvAExpr lv) n path)
    Nothing -> Left (Unbound n)

  -- Parameter uses look the param up by name (just like tyConRef),
  -- and likewise re-emit the path in the polymorphic output for
  -- downstream Stern-Gerlach disambiguation.
  tyParamRef _ann n path = HypLinf $ \env -> case Map.lookup n (hypLinfEnvNames env) of
    Just proc ->
      let lv = hRun proc
      in Right (HypLinfExpr proc, env, tyParamRef (LvAExpr lv) n path)
    Nothing -> Left (Unbound n)

  -- Homogeneous application: f and x must inhabit the same fibre.
  -- The application's level is f's level (= x's by the check).
  app _ann appPath f x = HypLinf $ \env -> do
    (vf, env1, polyF) <- runHypLinf f env
    (vx, env2, polyX) <- runHypLinf x env1
    let procF = hypLinfExprProc vf
        procX = hypLinfExprProc vx
        lvF   = hRun procF
        lvX   = hRun procX
    if lvF /= lvX
      then Left (LevelTear lvF lvX)
      else
        let lv = lvF
        in Right (HypLinfExpr procF, env2, app (LvAExpr lv) appPath polyF polyX)

  star _ann w = HypLinf $ \env -> do
    let lv   = starLevel w
        proc = hPure lv
    pure (HypLinfExpr proc, env, star (LvAExpr lv) w)

  arr _ann a b = HypLinf $ \env -> do
    (av, env1, polyA) <- runHypLinf a env
    (bv, env2, polyB) <- runHypLinf b env1
    let procA = hypLinfExprProc av
        procB = hypLinfExprProc bv
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
        in Right (HypLinfExpr procA, env2, arr (LvAExpr lv) polyA polyB)

  -- The parser resolved binder + use names to 'Path's; the carrier
  -- just uses them.
  forallLv _ann name binderPath body = HypLinf $ \env -> do
    (bv, env1, polyBody) <- runHypLinf body env
    let procBody = hypLinfExprProc bv
        lv = hRun procBody
    pure ( HypLinfExpr procBody
         , env1
         , forallLv (LvAExpr lv) name binderPath polyBody
         )

  starVar _ann name binderPath offset = HypLinf $ \env ->
    let lv = addOffset (LVar binderPath) offset
        proc = hPure lv
    in Right (HypLinfExpr proc, env, starVar (LvAExpr lv) name binderPath offset)

-- ----------------------------------------------------------------------
-- Solver: invoke each name's hyperfunction to extract its level.
-- ----------------------------------------------------------------------

solveLevelsHypLinf :: HypLinfResult -> Either LvErr LevelMap
solveLevelsHypLinf r = Right (Map.map hRun (hypLinfResultNames r))
