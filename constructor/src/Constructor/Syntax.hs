{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Constructor.Syntax
  ( Lang (..)
  , HasAnn (..)
  , Name
  ) where

import Constructor.Path (Path)
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
--
--   'forallLv' and 'starVar' carry universe polymorphism.  They have
--   error defaults so carriers that don't (yet) support polymorphism
--   can omit them — those carriers crash if asked to interpret a
--   polymorphic input, which is honest about what they support.
class Lang (r :: (Sort -> Type) -> Sort -> Type) where
  prog     :: a 'SProg -> [r a 'SDecl] -> r a 'SProg
  -- | Data declaration.  The @[Name]@ list is the parameter list
  --   (empty for non-parametric data).  Each parameter binds a type
  --   variable scoped over the body's constructor types.
  dataDecl :: a 'SDecl -> Name -> [Name] -> r a 'SExpr -> [r a 'SDecl] -> r a 'SDecl
  ctorDecl :: a 'SDecl -> Name -> r a 'SExpr -> r a 'SDecl
  var      :: a 'SExpr -> Name -> r a 'SExpr
  star     :: a 'SExpr -> Word -> r a 'SExpr
  arr      :: a 'SExpr -> r a 'SExpr -> r a 'SExpr -> r a 'SExpr
  -- | Type-level application: @f x@.  Left-associative
  --   juxtaposition at the surface; @f x y@ parses to @app (app f x) y@.
  --   Has an error default for carriers that don't (yet) support it.
  app      :: a 'SExpr -> r a 'SExpr -> r a 'SExpr -> r a 'SExpr
  app = error "Lang.app: application not supported by this carrier"

  -- | Level-binder introduction: @∀l. body@.  The @Name@ is the
  --   binder's surface name (for display); the @Path@ is its
  --   syntactic identity (replaces the counter-based fresh id).
  --   Inside @body@ the parser parses references to that name (in
  --   universe positions) via 'starVar' with the same 'Path'.
  forallLv :: a 'SExpr -> Name -> Path -> r a 'SExpr -> r a 'SExpr
  forallLv = error "Lang.forallLv: level polymorphism not supported by this carrier"

  -- | Variable-shifted universe: @*(l + n)@.  The @Name@ is the
  --   binder's surface name; the @Path@ is the binder's identity
  --   (resolved by the parser via name lookup); the @Word@ is the
  --   offset.  Bare @*l@ parses to @starVar ann l p 0@.
  starVar  :: a 'SExpr -> Name -> Path -> Word -> r a 'SExpr
  starVar  = error "Lang.starVar: level polymorphism not supported by this carrier"

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
