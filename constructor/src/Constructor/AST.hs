{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE StandaloneDeriving #-}

module Constructor.AST
  ( Tree (..)
  ) where

import Constructor.Path (Path)
import Constructor.Sort (Mode (..), Sort (..))
import Constructor.Syntax (Lang (..), Name)
import Data.Kind (Type)

-- | The initial-algebra carrier: a GADT indexed by sort and annotated
--   per node by the HKT'd annotation kind @a :: Sort -> Type@.  A
--   single 'Lang' instance covers every phase; specialise by choosing
--   the annotation type at the use site.
data Tree (a :: Sort -> Type) (s :: Sort) where
  Prog     :: a 'SProg -> [Tree a 'SDecl] -> Tree a 'SProg
  DataDecl :: a 'SDecl -> Path -> Name -> [(Name, Maybe (Tree a 'SExpr))] -> Tree a 'SExpr -> [Tree a 'SDecl] -> Tree a 'SDecl
  CtorDecl :: a 'SDecl -> Name -> Tree a 'SExpr -> Tree a 'SDecl
  Var      :: a 'SExpr -> Name -> Tree a 'SExpr
  Star     :: a 'SExpr -> Word -> Tree a 'SExpr
  Arr      :: a 'SExpr -> Tree a 'SExpr -> Tree a 'SExpr -> Tree a 'SExpr
  ForallLv :: a 'SExpr -> Name -> Path -> Tree a 'SExpr -> Tree a 'SExpr
  ExistsTy :: a 'SExpr -> Name -> Path -> Tree a 'SExpr -> Tree a 'SExpr
  StarVar  :: a 'SExpr -> Name -> Path -> Word -> Tree a 'SExpr
  App      :: a 'SExpr -> Path -> Tree a 'SExpr -> Tree a 'SExpr -> Tree a 'SExpr
  TyParamRef :: a 'SExpr -> Name -> Path -> Tree a 'SExpr
  TyConRef   :: a 'SExpr -> Name -> Path -> Tree a 'SExpr
  TyKindMeta :: a 'SExpr -> Path -> Tree a 'SExpr
  -- value-level / pattern-match constructors
  ValDecl    :: a 'SDecl -> Path -> Name -> Tree a ('SVal 'Build) -> Tree a 'SDecl
  ValVar     :: a ('SVal m) -> Name -> Path -> Tree a ('SVal m)
  ValWild    :: a ('SVal 'Dissect) -> Tree a ('SVal 'Dissect)
  ValCtor    :: a ('SVal m) -> Name -> Path -> [Tree a ('SVal m)] -> Tree a ('SVal m)
  Case       :: a ('SVal 'Build) -> Tree a ('SVal 'Build) -> [Tree a 'SArm] -> Tree a ('SVal 'Build)
  Arm        :: a 'SArm -> Tree a ('SVal 'Dissect) -> Tree a ('SVal 'Build) -> Tree a 'SArm
  ValAt      :: a ('SVal 'Dissect) -> Name -> Path -> Tree a ('SVal 'Dissect) -> Tree a ('SVal 'Dissect)
  -- value-level lambda + application (Haskell-style juxtaposition)
  ValLam     :: a ('SVal 'Build) -> Name -> Path -> Tree a ('SVal 'Build) -> Tree a ('SVal 'Build)
  ValApp     :: a ('SVal 'Build) -> Path -> Tree a ('SVal 'Build) -> Tree a ('SVal 'Build) -> Tree a ('SVal 'Build)

deriving instance (forall s. Show (a s)) => Show (Tree a t)
deriving instance (forall s. Eq   (a s)) => Eq   (Tree a t)

instance Lang Tree where
  prog     = Prog
  dataDecl = DataDecl
  ctorDecl = CtorDecl
  var      = Var
  star     = Star
  arr      = Arr
  forallLv   = ForallLv
  existsTy   = ExistsTy
  starVar    = StarVar
  app        = App
  tyParamRef = TyParamRef
  tyConRef   = TyConRef
  tyKindMeta = TyKindMeta
  valDecl    = ValDecl
  valVar     = ValVar
  valWild    = ValWild
  valCtor    = ValCtor
  case_      = Case
  arm        = Arm
  valAt      = ValAt
  valLam     = ValLam
  valApp     = ValApp
