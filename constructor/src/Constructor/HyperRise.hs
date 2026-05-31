{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE NoStarIsType #-}

-- | Hyper-rise: the staircase abstraction over a profunctor @p@.
--
-- The relative (non-level-annotated) form of the (γ) algebra from the
-- @38d9ed6@ git-note and the @Hyper-rise@ section of @PLAN.md@.
--
-- A 'Rise' is a coinductive tower whose every rung carries a value of
-- some profunctor-shaped type @p a b@.  'rise' decomposes a tower into
-- its bottom rung and the remaining staircase; 'retreat' reassembles.
-- They form a retraction: @retreat . rise = id@ always, and
-- @rise . retreat = id@ on the image of @rise@.
--
-- 'Γ' is the canonical instantiation @Gamma Hyper@ — the
-- hyperfunction tower.  'stepUp' (a.k.a. 'kindOf') is the abstract
-- upward move on any 'Rise'.
module Constructor.HyperRise
  ( -- * The Rise class
    Rise (..)
    -- * The canonical generic carrier
  , Gamma (..)
    -- * The hyperfunction-specific alias
  , Γ
    -- * Step / projection / build
  , stepUp
  , kindOf
  , current
  , unfoldRise
  ) where

import Data.Kind (Type)
import Constructor.HyperLite (Hyper)

-- | The staircase abstraction.
--
-- @r@ is the rise-carrier (the tower shape).  @p@ is the profunctor
-- (or profunctor-like) on each rung.  @a@ and @b@ are the lateral
-- parameters carried uniformly across rungs.
--
-- Laws (retraction):
--
-- > retreat . rise = id_{r p a b}                                   -- always
-- > rise . retreat = id_{(p a b, r p a b)}   -- on the image of rise
class Rise (r :: (Type -> Type -> Type) -> Type -> Type -> Type) where
  -- | Decompose a rise into its bottom rung and the staircase above.
  rise    :: r p a b -> (p a b, r p a b)
  -- | Reassemble a rise from a rung and a tail.  Inverse of 'rise' on
  --   well-formed pairs.
  retreat :: (p a b, r p a b) -> r p a b

-- | The canonical hyper-rise carrier: an infinite coinductive
-- staircase of @p a b@ rungs.
--
-- Strict on the current rung, lazy on the tail — so the tower can be
-- infinite (or stabilise coinductively at some fixed-point tail).
data Gamma (p :: Type -> Type -> Type) a b
  = Gamma { horizontal :: !(p a b)
          , vertical   ::   Gamma p a b
          }

instance Rise Gamma where
  rise    (Gamma h v) = (h, v)
  retreat (h, v)      = Gamma h v

-- | Hyper-rise over the canonical 'Hyper' profunctor — the (γ) of the
-- git-note framing.
type Γ = Gamma Hyper

-- | Abstract one-rung-up step on any 'Rise'.  Equivalent to
-- @snd . rise@.
--
-- For the concrete TyView tower in "Constructor.Tower", an
-- analogously-named (but type-specific) @kindOf@ does the same job;
-- this one is the polymorphic version that works for any 'Rise'
-- carrier and any rung profunctor.
stepUp :: Rise r => r p a b -> r p a b
stepUp = snd . rise

-- | Alias of 'stepUp', for vocabulary alignment with the typing tower.
kindOf :: Rise r => r p a b -> r p a b
kindOf = stepUp

-- | The current rung's profunctor.  Equivalent to @fst . rise@.
current :: Rise r => r p a b -> p a b
current = fst . rise

-- | Build a 'Gamma' tower from a seed rung and a one-step "next rung"
-- function.  Generates the column coinductively.
unfoldRise :: (p a b -> p a b) -> p a b -> Gamma p a b
unfoldRise step h0 = Gamma h0 (unfoldRise step (step h0))
