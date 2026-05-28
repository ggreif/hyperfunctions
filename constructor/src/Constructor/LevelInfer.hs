{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}

-- | Level inference for the constructor language, as a finally-tagless
--   carrier 'Lvl'.  Each subterm is assigned a 'Place' on the sheet; the
--   'Lang' methods emit unification/pinning constraints and the union-find
--   in "Constructor.Sheet" carries them.
--
--   This is the rehearsal for the eventual type-inference carrier: the
--   carrier shape (state-threading 'Place'-producing functions), the
--   substrate (union-find with pluggable merge), and the error story all
--   carry over.  What changes when type inference arrives: 'mergeLv'
--   becomes a recursive structural unification on type expressions.
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
  , envParent :: !(Maybe Place)      -- enclosing data's place, set by dataDecl
  } deriving Show

emptyEnv :: Env
emptyEnv = Env emptySheet Map.empty Nothing

-- | Errors surfaced by inference.
data LvErr
  = Unbound Name                     -- name used before declaration
  | Duplicate Name                   -- declared more than once
  | DataAnnotationTooLow Name Lv     -- @data X : E@ with @level(E)@ unable to host an inhabitant (@< 1@)
  | LevelTear Lv Lv                  -- two places forced equal but pinned to different levels
  | UnpinnedLevel                    -- internal: a place's level was not determined (should not happen in v0)
  | CtorOutsideData Name             -- internal sanity: a 'ctorDecl' fired outside a 'dataDecl'
  deriving (Eq, Show)

-- | v0 merge: two pinned levels agree iff equal.
mergeLv :: Lv -> Lv -> Either LvErr Lv
mergeLv a b
  | a == b    = Right a
  | otherwise = Left (LevelTear a b)

-- | Map a 'Sort' to its inferred output type.
type family LvOut (s :: Sort) :: Type where
  LvOut 'SProg = LevelMap
  LvOut 'SDecl = ()
  LvOut 'SExpr = Place

-- | The level-inference carrier.  An effectful function that threads 'Env'
--   and emits @LvOut s@ at sort @s@.
newtype Lvl (s :: Sort) = Lvl { runLvl :: Env -> Either LvErr (LvOut s, Env) }

-- | Run inference on a 'Lvl 'SProg' value.
inferProgram :: Lvl 'SProg -> Either LvErr LevelMap
inferProgram p = fst <$> runLvl p emptyEnv

-- | Numeric predecessor on 'Lv', undefined on @Z@.
predLv :: Lv -> Maybe Lv
predLv Z     = Nothing
predLv (S n) = Just n

-- | Bind a name to a place, failing on duplicates.
bind :: Name -> Place -> Env -> Either LvErr Env
bind n p env
  | Map.member n (envNames env) = Left (Duplicate n)
  | otherwise = Right env { envNames = Map.insert n p (envNames env) }

-- | Thread a list of declarations through the environment.
threadDecls :: [Lvl 'SDecl] -> Env -> Either LvErr Env
threadDecls []     env = Right env
threadDecls (d:ds) env = do
  (_, env') <- runLvl d env
  threadDecls ds env'

instance Lang Lvl where
  prog ds = Lvl $ \env -> do
    env' <- threadDecls ds env
    let sheet = envSheet env'
    pairs <- traverse (\(n, p) ->
                         case fst (levelOf p sheet) of
                           Just lv -> Right (n, lv)
                           Nothing -> Left UnpinnedLevel
                      ) (Map.toList (envNames env'))
    pure (Map.fromList pairs, env')

  dataDecl n e ds = Lvl $ \env -> do
    -- 1. Place + level of the universe annotation @E@.
    (pe, env1) <- runLvl e env
    let (mLe, sheet1) = levelOf pe (envSheet env1)
        env1' = env1 { envSheet = sheet1 }
    le <- maybe (Left UnpinnedLevel) Right mLe

    -- 2. @n@'s level = level(E) - 1; must succeed (the annotation must be at level >= 1).
    ln <- maybe (Left (DataAnnotationTooLow n le)) Right (predLv le)

    -- 3. Allocate place for @n@, pin its level, bind, set as the current parent.
    let (pn, sheet2) = freshPlace (envSheet env1')
    sheet3 <- pin mergeLv pn ln sheet2
    env2 <- bind n pn (env1' { envSheet = sheet3, envParent = Just pn })

    -- 4. Recurse into the body with @pn@ as the parent.
    env3 <- threadDecls ds env2

    -- 5. Restore the original parent (so sibling decls see the correct enclosing block).
    pure ((), env3 { envParent = envParent env1' })

  ctorDecl n t = Lvl $ \env -> do
    parent <- maybe (Left (CtorOutsideData n)) Right (envParent env)
    -- 1. Compute @t@'s place.
    (pt, env1) <- runLvl t env
    -- 2. Unify @t@ with the parent: a constructor's declared type must live at the
    --    enclosing data's level.  Homogeneous arrows propagate this through chains.
    sheet1 <- unify mergeLv pt parent (envSheet env1)
    -- 3. Compute the constructor's own level: parent's level minus one.
    let (mLp, sheet2) = levelOf parent sheet1
    lp <- maybe (Left UnpinnedLevel) Right mLp
    lc <- maybe (Left (DataAnnotationTooLow n lp)) Right (predLv lp)
    -- 4. Allocate place for the constructor, pin, bind.
    let (pc, sheet3) = freshPlace sheet2
    sheet4 <- pin mergeLv pc lc sheet3
    env2 <- bind n pc (env1 { envSheet = sheet4 })
    pure ((), env2)

  var x = Lvl $ \env -> case Map.lookup x (envNames env) of
    Just p  -> Right (p, env)
    Nothing -> Left (Unbound x)

  star w = Lvl $ \env -> do
    let (p, sheet1) = freshPlace (envSheet env)
    sheet2 <- pin mergeLv p (starLevel w) sheet1
    pure (p, env { envSheet = sheet2 })

  arr a b = Lvl $ \env -> do
    (pa, env1) <- runLvl a env
    (pb, env2) <- runLvl b env1
    -- Fresh place for the arrow itself, unified with both sides (homogeneous → in v0).
    let (parr, sheet0) = freshPlace (envSheet env2)
    sheet1 <- unify mergeLv pa pb sheet0
    sheet2 <- unify mergeLv parr pa sheet1
    pure (parr, env2 { envSheet = sheet2 })
