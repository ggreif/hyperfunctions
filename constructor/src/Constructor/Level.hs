module Constructor.Level
  ( Lv (..)
  , starLevel
  , succLv
  , addOffset
  ) where

import Constructor.Path (Path)

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
