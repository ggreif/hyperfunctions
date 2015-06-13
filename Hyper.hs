{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
module Hyper where

import Control.Arrow
-- import Control.Arrow.Transformer.CoState
import Control.Category
import Control.Monad.Fix
import Data.Coerce
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Functor.Product
import Data.Functor.Rep
import Data.Profunctor
import Data.Profunctor.Unsafe
import Data.Distributive
import Prelude hiding ((.),id)

-- | Hyperfunctions in explicit "Nu" form
--
-- 'arr' is a faithful functor, so
--
-- @'arr' f ≡ 'arr' g@ implies @f ≡ g@
--

data Hyper a b where
  Hyper :: ((x -> a) -> x -> b) -> x -> Hyper a b

instance Category Hyper where
  id = Hyper id ()
  Hyper f x . Hyper g y = Hyper (uncurry . collect f . collect g . curry) (x,y)

instance Arrow Hyper where
  arr f = Hyper (f.) ()

  first (Hyper f x) = Hyper f' x where
    f' fac = \ i -> (fb i, snd (fac i)) where
      fb = f (fst.fac)

  second (Hyper f x) = Hyper f' x where
    f' fca = \i -> (fst (fca i), fb i) where
      fb = f (snd.fca)

  Hyper f x *** Hyper g y = Hyper (h . curry) (x,y) where
    h fgac = \(i,j) -> (gfb j i, fgd i j) where
      fgd = g . (snd.) . fgac
      gfb j = f (\x -> fst $ fgac x j)

instance Profunctor Hyper where
  dimap f g (Hyper h x) = Hyper ((g.).h.(f.)) x

instance Strong Hyper where
  first' = first
  second' = second

instance Functor (Hyper a) where
  fmap f (Hyper h x) = Hyper ((f.).h) x

-- |
-- @
-- 'base' = 'arr' . 'const'
-- @
base :: b -> Hyper a b
base b = Hyper (\_ _ -> b) ()

-- | Unroll a hyperfunction
unroll :: Hyper a b -> (Hyper a b -> a) -> b
unroll (Hyper f x) k = f (k . Hyper f) x

-- | Re-roll a hyperfunction using Lambek's lemma.
roll :: ((Hyper a b -> a) -> b) -> Hyper a b
roll = Hyper (\ya xa2b -> xa2b (ya . unroll)) where

invoke :: Hyper a b -> Hyper b a -> b
invoke (Hyper f x) (Hyper g y) = r x y where
  r i j = f (\x -> g (r x) j) i

uninvoke :: (Hyper b a -> b) -> Hyper a b
uninvoke = Hyper $ \x f -> f (roll x)

-- |
-- @
-- 'arr' f ≡ 'push' f ('arr' f)
-- 'invoke' ('push' f q) k ≡ f ('invoke' k q)
-- 'push' f p . 'push' g q ≡ 'push' (f . g) (p . q)
-- @
push :: (a -> b) -> Hyper a b -> Hyper a b
push f q = uninvoke $ \k -> f (invoke k q)

-- |
-- @
-- 'run' f ≡ 'invoke' f 'id'
-- 'run' ('arr' f) = 'fix' f
-- 'run' ('push' f p . q) = f ('run' (q . p)) = f ('invoke' q p)
-- @
run :: Hyper a a -> a
run (Hyper f x) = fix f x

-- |
-- @
-- 'project' . 'arr' ≡ 'id'
-- 'project' h a ≡ 'invoke' h ('base' a)
-- @
project :: Hyper a b -> a -> b
project (Hyper f x) a = f (const a) x

-- |
-- <http://arxiv.org/pdf/1309.5135.pdf Under "nice" conditions>
--
-- @
-- 'fold' . 'build' = 'id'
-- @
fold :: [a] -> (a -> b -> c) -> c -> Hyper b c
fold [] _ n = base n
fold (x:xs) c n = push (c x) (fold xs c n)

build :: (forall b c. (a -> b -> c) -> c -> Hyper b c) -> [a]
build g = run (g (:) [])

-- ana :: CoStateArrow x (->) a b -> x -> Hyper a b
-- ana (CoStateArrow p) = Hyper p
