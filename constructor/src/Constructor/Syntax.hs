{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}

module Constructor.Syntax
  ( Lang (..)
  , Name
  ) where

import Constructor.Sort (Sort (..))
import Data.Kind (Type)
import Data.Text (Text)

-- | Identifiers (declared names, variable references).
type Name = Text

-- | Finally-tagless algebra for the constructor language.
--
--   A single carrier @r :: Sort -> Type@ ranges over all three syntactic
--   sorts: programs, declarations, and expressions.  Each method emits a
--   piece of grammar at the appropriate sort.
class Lang (r :: Sort -> Type) where
  -- | A program is a sequence of top-level declarations.
  prog     :: [r 'SDecl] -> r 'SProg

  -- | @data X : E { … }@ — declares a new data type @X@ whose universe is @E@
  --   and whose body is a list of inner declarations (constructors or
  --   nested data).
  dataDecl :: Name -> r 'SExpr -> [r 'SDecl] -> r 'SDecl

  -- | A constructor declaration @c : T@ inside a @data@ block.  @T@ is the
  --   constructor's type — a chain of (homogeneous) arrows ending in the
  --   enclosing data's name.
  ctorDecl :: Name -> r 'SExpr -> r 'SDecl

  -- | Reference a declared name.
  var      :: Name -> r 'SExpr

  -- | The universe @*n@.  The 'Word' is the surface decimal @n@; the
  --   tower-level it occupies is @n + 2@ (see "Constructor.Level").
  star     :: Word -> r 'SExpr

  -- | Function arrow.  v0 enforces homogeneity: both sides must end up
  --   at the same level after inference.
  arr      :: r 'SExpr -> r 'SExpr -> r 'SExpr
