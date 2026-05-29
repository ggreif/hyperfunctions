{-# LANGUAGE RankNTypes #-}

-- | A minimal inlined hyperfunction type for the level-inference warm-up.
--
--   Inlined rather than depending on the upstream @hyperfunctions@ package
--   because that package's @transformers < 0.5@ bound conflicts with the
--   transformers shipped by GHC 9.10.  Once we want @Category@,
--   @Profunctor@, @Arrow@, etc. (for the real type-inference experiment),
--   we can switch to the library — or relax its bounds locally.  For now,
--   bare @hPure@ and @hRun@ are enough.
module Constructor.HyperLite
  ( Hyper (..)
  , hPure
  , hRun
  ) where

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
