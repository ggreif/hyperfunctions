{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}

-- | Hyperfunction-backed level inference (warm-up rehearsal).
--
--   Functionally identical to "Constructor.LevelInfer": the algorithm is
--   the same and produces the same 'LevelMap'.  The difference is that
--   each subterm's level is carried as a @Hyper Lv Lv@ rather than a raw
--   'Lv'.  Self-application ('hRun') is the extraction operation; values
--   travel as constant hyperfunctions ('hPure').
--
--   At this stage the encoding adds no power — levels are flat scalars,
--   so the hyperfunction collapses to its constant.  The point is to
--   confirm the carrier shape works under 'Lang' and to leave the seam
--   visible for the type-inference experiment, where the algebraic
--   structure of hyperfunctions starts paying off (recursive type
--   processes, negotiation via self-application, etc.).
module Constructor.HfLvl
  ( HfLvl
  , inferProgramHf
  ) where

import Constructor.HyperLite (Hyper, hPure, hRun)
import Constructor.Level (Lv (..), addOffset, starLevel)
import Constructor.LevelInfer (LevelMap, LvErr (..))
import Constructor.Sort (Sort (..))
import Constructor.Syntax (Lang (..), Name)
import Data.Kind (Type)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

-- | A level-process: a hyperfunction wrapping a level.
type LvProc = Hyper Lv Lv

fromLv :: Lv -> LvProc
fromLv = hPure

extract :: LvProc -> Lv
extract = hRun

data Env = Env
  { envNames     :: !(Map Name LvProc)
  , envParent    :: !(Maybe LvProc)
  , envLvBinders :: !(Map Name Int)
  , envNextLVar  :: !Int
  }

emptyEnv :: Env
emptyEnv = Env Map.empty Nothing Map.empty 0

type family HfOut (s :: Sort) :: Type where
  HfOut 'SProg = LevelMap
  HfOut 'SDecl = ()
  HfOut 'SExpr = LvProc

-- | The hyperfunction-backed level-inference carrier.  Phantom in @a@.
newtype HfLvl (a :: Sort -> Type) (s :: Sort) = HfLvl
  { runHfLvl :: Env -> Either LvErr (HfOut s, Env) }

inferProgramHf :: HfLvl a 'SProg -> Either LvErr LevelMap
inferProgramHf p = fst <$> runHfLvl p emptyEnv

predLv :: Lv -> Maybe Lv
predLv Z        = Nothing
predLv (S n)    = Just n
predLv (LVar _) = Nothing   -- polymorphic levels: unsupported here

bind :: Name -> LvProc -> Env -> Either LvErr Env
bind n p env
  | Map.member n (envNames env) = Left (Duplicate n)
  | otherwise = Right env { envNames = Map.insert n p (envNames env) }

threadDecls :: [HfLvl a 'SDecl] -> Env -> Either LvErr Env
threadDecls []     env = Right env
threadDecls (d:ds) env = do
  (_, env') <- runHfLvl d env
  threadDecls ds env'

-- | Two level-processes "negotiate" by both self-applying and comparing.
--   In v0 this is equivalent to direct 'Lv' comparison; the
--   hyperfunction step is the seam.
unifyProcs :: LvProc -> LvProc -> Either LvErr LvProc
unifyProcs a b
  | la == lb  = Right a
  | otherwise = Left (LevelTear la lb)
  where
    la = extract a
    lb = extract b

instance Lang HfLvl where
  prog _ann ds = HfLvl $ \env -> do
    env' <- threadDecls ds env
    let finals = [ (n, extract proc) | (n, proc) <- Map.toList (envNames env') ]
    pure (Map.fromList finals, env')

  dataDecl _ann n e ds = HfLvl $ \env -> do
    (procE, env1) <- runHfLvl e env
    let le = extract procE
    ln <- maybe (Left (DataAnnotationTooLow n le)) Right (predLv le)
    let procN = fromLv ln
    env2 <- bind n procN (env1 { envParent = Just procN })
    env3 <- threadDecls ds env2
    pure ((), env3 { envParent = envParent env1 })

  ctorDecl _ann n t = HfLvl $ \env -> do
    parent <- maybe (Left (CtorOutsideData n)) Right (envParent env)
    (procT, env1) <- runHfLvl t env
    _ <- unifyProcs procT parent
    let lp = extract parent
    lc <- maybe (Left (DataAnnotationTooLow n lp)) Right (predLv lp)
    let procC = fromLv lc
    env2 <- bind n procC env1
    pure ((), env2)

  var _ann x = HfLvl $ \env -> case Map.lookup x (envNames env) of
    Just p  -> Right (p, env)
    Nothing -> Left (Unbound x)

  star _ann w = HfLvl $ \env -> Right (fromLv (starLevel w), env)

  arr _ann a b = HfLvl $ \env -> do
    (pa, env1) <- runHfLvl a env
    (pb, env2) <- runHfLvl b env1
    procR <- unifyProcs pa pb
    pure (procR, env2)

  forallLv _ann n body = HfLvl $ \env -> do
    let i = envNextLVar env
        env1 = env { envNextLVar  = i + 1
                   , envLvBinders = Map.insert n i (envLvBinders env)
                   }
    (procBody, env2) <- runHfLvl body env1
    pure (procBody, env2 { envLvBinders = envLvBinders env })

  starVar _ann n offset = HfLvl $ \env -> case Map.lookup n (envLvBinders env) of
    Just i  -> Right (fromLv (addOffset (LVar i) offset), env)
    Nothing -> Left (Unbound n)
