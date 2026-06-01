{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}

module Constructor.Level
  ( Lv (..)
  , starLevel
  , succLv
  , addOffset
    -- * Level-inference domain types (carrier-agnostic)
  , LvErr (..)
  , LevelMap
  , LvAnnot (..)
  , Shape (..)
  ) where

import Constructor.Path (Path)
import Constructor.Sort (Sort (..))
import Constructor.Syntax (Name)
import Data.Map.Strict (Map)

-- | Internal unary representation of universe levels, extended with
--   level variables to support universe polymorphism.
--
--   The surface syntax @*n@ (decimal @n@) desugars to a universe term
--   tagged with @n@; surface @*(l + k)@ desugars to @k@ applications of
--   'S' wrapped around @LVar p@, where @p@ is the path of the '∀l.'
--   binder that introduced the variable.  Anchor: @level(*0) = 2@.
--
--   Binder identity is path-derived (no counter, no multi-instantiation
--   freshness — see "Constructor.Path" for the rationale).
data Lv = Z | S !Lv | LVar !Path
  deriving (Eq, Ord, Show)

-- | @starLevel n@ is the level of the universe written @*n@: that is, @n + 2@.
starLevel :: Word -> Lv
starLevel = go . (+ 2)
  where
    go 0 = Z
    go k = S (go (k - 1))

succLv :: Lv -> Lv
succLv = S

-- | Wrap an 'Lv' in @n@ applications of 'S'.  Used to expand the
--   surface @l + n@ shorthand into a Peano-style stack of successors:
--   @addOffset (LVar i) 3 = S (S (S (LVar i)))@.
addOffset :: Lv -> Word -> Lv
addOffset l 0 = l
addOffset l n = S (addOffset l (n - 1))

-- ----------------------------------------------------------------------
-- Level-inference domain types
--
-- These are the carrier-agnostic result/error/annotation types of
-- level inference.  They outlived the Sheet-based inferencers
-- (Constructor.Tc / .LevelInfer, removed): the Hyper-based pipeline
-- (HypLinf etc.) produces and consumes them just the same, so they
-- live here in the level domain rather than inside any one carrier.
-- ----------------------------------------------------------------------

-- | Errors raised during level inference.
data LvErr
  = Unbound Name
  | Duplicate Name
  | DataAnnotationTooLow Name Lv
  | LevelTear Lv Lv
  | UnpinnedLevel
  | CtorOutsideData Name
  deriving (Eq, Show)

-- | The solved result: each top-level binder's inferred level.
type LevelMap = Map Name Lv

-- | Annotation carrying the inferred level at each node, plus a
--   'Shape' classifying whether the node's kind is classical
--   (universe-level), iso-tower self-referential, or an unresolved
--   kind-meta to be pinned at use sites.
data LvAnnot (s :: Sort) where
  LvAExpr :: !Lv -> !Shape -> LvAnnot 'SExpr
  LvADecl :: !Lv -> !Shape -> LvAnnot 'SDecl
  LvAProg ::                  LvAnnot 'SProg

deriving instance Show (LvAnnot s)
deriving instance Eq (LvAnnot s)

-- | The kind-shape dimension that travels alongside the universe
--   level in 'LvAnnot'.  Co-evolves with the level during inference:
--   resolution of a kind-meta resolves both the level and the shape
--   together.
data Shape = Classical
              -- ^ Universe-level kind ('*0', '*1', …).  The "sticky"
              --   shape that blocks the demote-interp-promote slide.
           | IsoTower !Name
              -- ^ Self-referential kind on the named tycon (the
              --   covering-space form: @data Bool⋮@ etc.).  Slidable.
           | IsoTowerMeta !Path
              -- ^ Unresolved kind-meta; resolves to 'Classical' or
              --   'IsoTower' at the meta's use site.  Defaults to
              --   'Classical' at end-of-elaboration when no resolution
              --   has occurred.  Path identifies the meta's
              --   allocation site.
  deriving (Eq, Show)
