{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}

module Constructor.AST
  ( Tree (..)
  ) where

import Constructor.Sort (Sort (..))
import Constructor.Syntax (Lang (..), Name)

-- | The initial-algebra carrier: a plain ADT (GADT, since sorts are
--   tracked statically).  Re-emits everything mechanically.
data Tree (s :: Sort) where
  Prog     :: [Tree 'SDecl] -> Tree 'SProg
  DataDecl :: Name -> Tree 'SExpr -> [Tree 'SDecl] -> Tree 'SDecl
  CtorDecl :: Name -> Tree 'SExpr -> Tree 'SDecl
  Var      :: Name -> Tree 'SExpr
  Star     :: Word -> Tree 'SExpr
  Arr      :: Tree 'SExpr -> Tree 'SExpr -> Tree 'SExpr

deriving instance Show (Tree s)
deriving instance Eq (Tree s)

instance Lang Tree where
  prog     = Prog
  dataDecl = DataDecl
  ctorDecl = CtorDecl
  var      = Var
  star     = Star
  arr      = Arr
