{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Constructor.Syntax
  ( Lang (..)
  , HasAnn (..)
  , Name
  ) where

import Constructor.Sort (Sort (..))
import Data.Functor.Const (Const (..))
import Data.Kind (Type)
import Data.Text (Text)

-- | Identifiers (declared names, variable references).
type Name = Text

-- | Finally-tagless algebra for the constructor language, HKT'd in the
--   annotation kind @a :: Sort -> Type@ (Trees-that-Grow style).  Each
--   method takes a per-sort annotation slot; instances are usually
--   polymorphic in @a@ and just thread it through.  See 'HasAnn' for
--   the convention by which producers (e.g. the parser) obtain
--   annotation values without committing to a particular phase.
class Lang (r :: (Sort -> Type) -> Sort -> Type) where
  prog     :: a 'SProg -> [r a 'SDecl] -> r a 'SProg
  dataDecl :: a 'SDecl -> Name -> r a 'SExpr -> [r a 'SDecl] -> r a 'SDecl
  ctorDecl :: a 'SDecl -> Name -> r a 'SExpr -> r a 'SDecl
  var      :: a 'SExpr -> Name -> r a 'SExpr
  star     :: a 'SExpr -> Word -> r a 'SExpr
  arr      :: a 'SExpr -> r a 'SExpr -> r a 'SExpr -> r a 'SExpr

-- | Annotation provider in an applicative monad @m@.  The parser is
--   written generically against 'HasAnn', so it can produce trees at
--   any annotation regime without further refactoring.
class Applicative m => HasAnn (a :: Sort -> Type) (m :: Type -> Type) where
  freshExprAnn :: m (a 'SExpr)
  freshDeclAnn :: m (a 'SDecl)
  freshProgAnn :: m (a 'SProg)

-- | Trivial annotations: every slot is @Const ()@.  Works for any
--   applicative monad — the raw-parsing default.
instance Applicative m => HasAnn (Const ()) m where
  freshExprAnn = pure (Const ())
  freshDeclAnn = pure (Const ())
  freshProgAnn = pure (Const ())
