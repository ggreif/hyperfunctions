{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}

-- | Level inference for the constructor language, as a finally-tagless
--   carrier 'Lvl'.  Each subterm is assigned a 'Place' on the sheet;
--   the 'Lang' methods emit unification/pinning constraints carried by
--   the union-find in "Constructor.Sheet".
--
--   The carrier ignores the HKT annotation slot @a@ — level inference
--   discovers its own info through the substrate, so user-supplied
--   annotations are phantom here.  This is the rehearsal pattern for
--   type inference: the carrier holds whatever it needs internally,
--   the annotation slot is just there to keep the 'Lang' signature
--   uniform across phases.
module Constructor.LevelInfer
  ( Lvl
  , inferProgram
  , LvErr (..)
  , LevelMap
  ) where

import Constructor.Level (Lv (..), starLevel)
import Constructor.Sheet
import Constructor.Sort (Sort (..))
import Constructor.Syntax (Lang (..), Name)
import Data.Kind (Type)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

-- | Outcome of a successful level inference: declared names → their levels.
type LevelMap = Map Name Lv

data Env = Env
  { envSheet  :: !(Sheet Lv)
  , envNames  :: !(Map Name Place)   -- declared name → its place
  , envParent :: !(Maybe Place)      -- enclosing data's place, set by 'dataDecl'
  } deriving Show

emptyEnv :: Env
emptyEnv = Env emptySheet Map.empty Nothing

-- | Errors surfaced by inference.
data LvErr
  = Unbound Name
  | Duplicate Name
  | DataAnnotationTooLow Name Lv
  | LevelTear Lv Lv
  | UnpinnedLevel
  | CtorOutsideData Name
  deriving (Eq, Show)

mergeLv :: Lv -> Lv -> Either LvErr Lv
mergeLv a b
  | a == b    = Right a
  | otherwise = Left (LevelTear a b)

-- | Per-sort output of the inference carrier.
type family LvOut (s :: Sort) :: Type where
  LvOut 'SProg = LevelMap
  LvOut 'SDecl = ()
  LvOut 'SExpr = Place

-- | The level-inference carrier.  Phantom in @a@ — the annotation slot
--   is provided by the 'Lang' signature but unused here.
newtype Lvl (a :: Sort -> Type) (s :: Sort) = Lvl
  { runLvl :: Env -> Either LvErr (LvOut s, Env) }

-- | Run inference on a 'Lvl' program value.
inferProgram :: Lvl a 'SProg -> Either LvErr LevelMap
inferProgram p = fst <$> runLvl p emptyEnv

predLv :: Lv -> Maybe Lv
predLv Z        = Nothing
predLv (S n)    = Just n
predLv (LVar _) = Nothing   -- polymorphic levels: unsupported here

bind :: Name -> Place -> Env -> Either LvErr Env
bind n p env
  | Map.member n (envNames env) = Left (Duplicate n)
  | otherwise = Right env { envNames = Map.insert n p (envNames env) }

threadDecls :: [Lvl a 'SDecl] -> Env -> Either LvErr Env
threadDecls []     env = Right env
threadDecls (d:ds) env = do
  (_, env') <- runLvl d env
  threadDecls ds env'

instance Lang Lvl where
  prog _ann ds = Lvl $ \env -> do
    env' <- threadDecls ds env
    let sheet = envSheet env'
    pairs <- traverse (\(n, p) ->
                         case fst (levelOf p sheet) of
                           Just lv -> Right (n, lv)
                           Nothing -> Left UnpinnedLevel
                      ) (Map.toList (envNames env'))
    pure (Map.fromList pairs, env')

  dataDecl _ann n e ds = Lvl $ \env -> do
    (pe, env1) <- runLvl e env
    let (mLe, sheet1) = levelOf pe (envSheet env1)
        env1' = env1 { envSheet = sheet1 }
    le <- maybe (Left UnpinnedLevel) Right mLe
    ln <- maybe (Left (DataAnnotationTooLow n le)) Right (predLv le)
    let (pn, sheet2) = freshPlace (envSheet env1')
    sheet3 <- pin mergeLv pn ln sheet2
    env2 <- bind n pn (env1' { envSheet = sheet3, envParent = Just pn })
    env3 <- threadDecls ds env2
    pure ((), env3 { envParent = envParent env1' })

  ctorDecl _ann n t = Lvl $ \env -> do
    parent <- maybe (Left (CtorOutsideData n)) Right (envParent env)
    (pt, env1) <- runLvl t env
    sheet1 <- unify mergeLv pt parent (envSheet env1)
    let (mLp, sheet2) = levelOf parent sheet1
    lp <- maybe (Left UnpinnedLevel) Right mLp
    lc <- maybe (Left (DataAnnotationTooLow n lp)) Right (predLv lp)
    let (pc, sheet3) = freshPlace sheet2
    sheet4 <- pin mergeLv pc lc sheet3
    env2 <- bind n pc (env1 { envSheet = sheet4 })
    pure ((), env2)

  var _ann x = Lvl $ \env -> case Map.lookup x (envNames env) of
    Just p  -> Right (p, env)
    Nothing -> Left (Unbound x)

  star _ann w = Lvl $ \env -> do
    let (p, sheet1) = freshPlace (envSheet env)
    sheet2 <- pin mergeLv p (starLevel w) sheet1
    pure (p, env { envSheet = sheet2 })

  arr _ann a b = Lvl $ \env -> do
    (pa, env1) <- runLvl a env
    (pb, env2) <- runLvl b env1
    let (parr, sheet0) = freshPlace (envSheet env2)
    sheet1 <- unify mergeLv pa pb sheet0
    sheet2 <- unify mergeLv parr pa sheet1
    pure (parr, env2 { envSheet = sheet2 })
