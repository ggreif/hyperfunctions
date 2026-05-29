module Constructor.Level
  ( Lv (..)
  , starLevel
  , succLv
  , addOffset
  ) where

-- | Internal unary representation of universe levels, extended with
--   level variables to support universe polymorphism.
--
--   The surface syntax @*n@ (decimal @n@) desugars to a universe term
--   tagged with @n@; surface @*(l + k)@ desugars to @k@ applications of
--   'S' wrapped around @LVar i@, where @i@ is the level binder's
--   identifier.  Anchor: @level(*0) = 2@, which follows from
--   @*n : *(n+1)@ coinductively and @level(x : T) = level(T) − 1@.
--
--   With 'LVar' present, unification on 'Lv' becomes Robinson-style
--   (five cases) rather than plain equality.
data Lv = Z | S !Lv | LVar !Int
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
