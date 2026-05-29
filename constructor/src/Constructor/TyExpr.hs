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

-- | Value-level types.  Type-variable identity is by 'Path' — the
--   parser supplies the binder's path so two distinct parameter
--   declarations with the same surface name are distinguishable
--   (the Stern-Gerlach reading: paths get fine-structure that the
--   surface name doesn't see).
data TyExpr
  = TyVar  !Name !Path            -- ^ type variable: surface name + binder path
  | TyCon  !Name                  -- ^ nullary type-constructor reference
  | TyApp  !TyExpr !TyExpr        -- ^ type application: @f x@
  | TyArr  !TyExpr !TyExpr        -- ^ function type: @a -> b@
  | TyUniv !Lv                    -- ^ universe at the given level
  deriving (Eq, Ord, Show)

-- | Compact pretty representation, useful in tests + error messages.
--   Drops the path; users see only the surface name.
prettyTy :: TyExpr -> Text
prettyTy = go
  where
    go (TyVar n _)     = n
    go (TyCon n)       = n
    go (TyApp f x)     = goAtom f <> " " <> goAtom x
    go (TyArr a b)     = goAtom a <> " -> " <> go b
    go (TyUniv l)      = "*" <> T.pack (show l)

    goAtom t@(TyArr _ _) = "(" <> go t <> ")"
    goAtom t@(TyApp _ _) = "(" <> go t <> ")"
    goAtom t             = go t
