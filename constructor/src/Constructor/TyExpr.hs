-- | Type expressions for the type-inference layer.
--
--   'TyExpr' represents value-level types — what appears to the right
--   of @:@ in a constructor declaration.  Distinct from the universe
--   layer ('Lv'), which counts the height in the typing tower; here
--   we represent the structural shape of types at level 1
--   ('Type'-kinded things), with universes folded in via 'TyUniv'
--   when they appear in type-expression position (rare in v0_polyType).
--
--   Currently type-variable identity is by 'Name' — sufficient for the
--   single-declaration scope where a 'data List a' introduces 'a' as
--   a variable for its own body.  A later commit will switch this to
--   'Path'-based identity, reusing the "Constructor.Path" machinery,
--   when multi-site instantiation of parametric data forces fresh-α
--   identities per use site.
{-# LANGUAGE OverloadedStrings #-}

module Constructor.TyExpr
  ( TyExpr (..)
  , prettyTy
  ) where

import Constructor.Level (Lv)
import Constructor.Path (Path)
import Constructor.Syntax (Name)
import Data.Text (Text)
import qualified Data.Text as T

-- | Value-level types.  Both type variables and type constructors
--   are identified by their declaration 'Path' (in addition to their
--   surface name, which is kept for display): the parser hands a
--   resolved binder path at every use site.  For nullary binders
--   the use-path collapses to the def-path \(x^0 = 1\); for
--   higher-kinded uses the path machinery extends naturally to
--   address instantiation freshness.
data TyExpr
  = TyVar   !Name !Path           -- ^ type variable; identified by binder path
  | TyCon   !Name !Path           -- ^ nullary type constructor; identified by decl path
  | TyApp   !TyExpr !TyExpr       -- ^ type application: @f x@
  | TyArr   !TyExpr !TyExpr       -- ^ function type: @a -> b@
  | TyUniv  !Lv                   -- ^ universe at the given level
  | TyDefer !Name !Path           -- ^ deferred value-level reference (a 'let'
                                  --   binding used in a type position).  The
                                  --   slide-down rule in HypTwr.var emits this;
                                  --   future phases will reduce 'TyApp (TyDefer
                                  --   f _) args' via the value-level
                                  --   interpreter.
  deriving (Eq, Ord, Show)

-- | Compact pretty representation, useful in tests + error messages.
--   Drops paths; users see only surface names.
prettyTy :: TyExpr -> Text
prettyTy = go
  where
    go (TyVar n _)     = n
    go (TyCon n _)     = n
    go (TyApp f x)     = goAtom f <> " " <> goAtom x
    go (TyArr a b)     = goAtom a <> " -> " <> go b
    go (TyUniv l)      = "*" <> T.pack (show l)
    go (TyDefer n _)   = n  -- print surface name; "deferred" tag elided

    goAtom t@(TyArr _ _) = "(" <> go t <> ")"
    goAtom t@(TyApp _ _) = "(" <> go t <> ")"
    goAtom t             = go t
