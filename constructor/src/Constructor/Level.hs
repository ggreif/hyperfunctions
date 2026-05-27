module Constructor.Level
  ( Lv (..)
  , starLevel
  , succLv
  ) where

-- | Internal unary representation of universe levels.
--
--   The surface syntax @*n@ (decimal @n@) desugars to a universe term
--   tagged with @n@; whenever the typechecker needs a concrete level
--   it uses 'starLevel' below.  Anchor: @level(*0) = 2@, which follows
--   from @*n : *(n+1)@ coinductively and @level(x : T) = level(T) − 1@.
data Lv = Z | S Lv
  deriving (Eq, Ord, Show)

-- | @starLevel n@ is the level of the universe written @*n@: that is, @n + 2@.
starLevel :: Word -> Lv
starLevel = go . (+ 2)
  where
    go 0 = Z
    go k = S (go (k - 1))

succLv :: Lv -> Lv
succLv = S
