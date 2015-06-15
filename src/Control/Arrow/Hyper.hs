{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Control.Arrow.Hyper where

import Control.Applicative
import Control.Arrow
import Control.Category
import Control.Monad.Fix
import Data.Coerce
import Data.Profunctor
import Prelude hiding ((.),id)

-- |
--
-- @
-- 'runHyper' f g = 'run' (f . g)
-- 'arr' f = 'push' f ('arr' f)
-- 'runHyper' id id = _|_
-- @
--
-- 'arr' is a faithful functor, so
--
-- @'arr' f ≡ 'arr' g@ implies @f ≡ g@
--
newtype Hyper a b = Hyper { runHyper :: Hyper b a -> b }

unroll :: Hyper a b -> (Hyper a b -> a) -> b
unroll = coerce

roll :: ((Hyper a b -> a) -> b) -> Hyper a b
roll = coerce

ana :: (x -> (x -> a) -> b) -> x -> Hyper a b
ana psi = f where f x = Hyper $ \z -> psi x (runHyper z . f)

-- | From "Generalizing the augment combinator" by Ghani, Uustali and Vene.
--
-- @
-- 'cata' phi ('push' f h) = phi $ \g -> f $ g ('cata' phi h)
-- @
cata :: (((x -> a) -> b) -> x) -> Hyper a b -> x
cata phi = f where f h = phi $ \g -> unroll h (g . f)

instance Category Hyper where
  id = arr id
  f . g = Hyper $ \k -> runHyper f (g . k)

instance Profunctor Hyper where
  dimap f g h = Hyper $ g . runHyper h . dimap g f
  lmap f h = Hyper $ runHyper h . rmap f
  rmap f h = Hyper $ f . runHyper h . lmap f

instance Arrow Hyper where
  arr = fix . push
  first = ana $ \i fac -> (unroll i (fst . fac), snd (fac i))
  second = ana $ \i fca -> (fst (fca i), unroll i (snd . fca))
  (***) = curry $ ana $ \(i,j) fgac -> (unroll i $ \i' -> fst $ fgac (i',j), unroll j $ \j' -> snd $ fgac (i,j'))
  (&&&) = curry $ ana $ \(i,j) fga  -> (unroll i $ \i' ->       fga  (i',j), unroll j $ \j' ->       fga  (i,j'))

instance ArrowLoop Hyper where
  loop = ana (flip f') where
    f' fa = fmap fst $ fix $ \r -> flip unroll $ \i -> (fa i, snd $ r i)

instance Strong Hyper where
  first' = first
  second' = second

instance Costrong Hyper where
  unfirst = loop

instance Functor (Hyper a) where
  fmap = rmap

instance Applicative (Hyper a) where
  pure a = Hyper $ \_ -> a
  p <* _ = p
  _ *> p = p
  (<*>) = curry $ ana $ \(i,j) fga ->
    unroll i (\i' -> fga (i',j)) $ unroll j (\j' -> fga (i,j'))

instance Monad (Hyper a) where
  return = pure
  m >>= f = cata (\g -> roll $ \k -> unroll (f (g k)) k) m

-- |
-- @
-- push f p . push g q = push (f . g) (p . q)
-- runHyper (push f p) q = f (runHyper q p)
-- @
push :: (a -> b) -> Hyper a b -> Hyper a b
push f q = Hyper $ \k -> f (runHyper k q)


-- |
--
-- @
-- 'run' ('arr' f) = 'fix' f
-- 'run' ('push' f q) = f ('run' q)
-- 'run' ('push' f p . q) = f ('run' (q . p)) = f ('runHyper' q p)
-- @
run :: Hyper a a -> a
run f = runHyper f id

-- |
-- 'project' is a left inverse for 'arr':
--
-- @
-- 'project' '.' 'arr' = 'id'
-- 'project' ('push' f q) = f
-- @
project :: Hyper a b -> a -> b
project q x = runHyper q (pure x)

fold :: [a] -> (a -> b -> c) -> c -> Hyper b c
fold xs c n = foldr (push . c) (pure n) xs

-- |
-- <http://arxiv.org/pdf/1309.5135.pdf Under nice conditions>
--
-- @
-- 'fold' . 'build' = 'id'
-- @
build :: (forall b c. (a -> b -> c) -> c -> Hyper b c) -> [a]
build g = run (g (:) [])
