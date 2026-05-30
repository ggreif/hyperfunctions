{-# LANGUAGE RankNTypes #-}

-- | A minimal inlined hyperfunction type for the level-inference warm-up.
--
--   Inlined rather than depending on the upstream @hyperfunctions@ package
--   because that package's @transformers < 0.5@ bound conflicts with the
--   transformers shipped by GHC 9.10.  Now carries the 'Category' instance
--   (Ed Kmett's encoding for this exact 'Hyper' shape) — needed once the
--   tower-aware meet starts composing vertical-meet steps along the
--   directed @:@-arrow.  'Profunctor' / 'Arrow' can land alongside when
--   downstream code wants them.
module Constructor.HyperLite
  ( Hyper (..)
  , hPure
  , hRun
  ) where

import Control.Category (Category (..))
import Prelude hiding (id, (.))

-- | The classical hyperfunction: a callback receiver.  Feeding it a
--   peer-callback @Hyper b a@ yields a @b@.  Self-application gives the
--   fixed-point semantics — see 'hRun'.
newtype Hyper a b = Hyper { invoke :: Hyper b a -> b }

-- | Constant hyperfunction: ignores its peer, always returns @b@.
hPure :: b -> Hyper a b
hPure b = Hyper (\_ -> b)

-- | Self-apply a same-typed hyperfunction.  For @hPure n@ this just
--   returns @n@; in general it unfolds the fixed point until the
--   hyperfunction's behaviour resolves to a value.
hRun :: Hyper a a -> a
hRun h = invoke h (Hyper hRun)

-- | Ed Kmett's 'Category' instance for the @Hyper a b = Hyper (Hyper b
--   a -> b)@ shape.  Composition feeds the peer through the right-hand
--   morphism before invoking the left; identity is the self-referential
--   hyperfunction that re-invokes its peer against itself, matching
--   'hRun' for the same-type case.
instance Category Hyper where
  id = self where self = Hyper $ \k -> invoke k self
  Hyper f . Hyper g = Hyper $ \k -> f (Hyper g . k)
