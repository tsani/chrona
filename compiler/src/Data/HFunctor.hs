{-|
Module      : Data.HFunctor
Description : Polykinded higher-order functors
Copyright   : (c) Jacob Errington 2017
License     : MIT
Maintainer  : chrona@mail.jerrington.me
Stability   : experimental

Polykinded higher-order functors allow you to represent indexed syntax trees.
Examples of indexed syntax trees include syntax trees with (static) type
annotations and mutual recursion.
-}

{-# LANGUAGE UndecidableInstances #-}

module Data.HFunctor
( -- * Natural transformations
  type (:~>)
  -- * Higher-order functors
, HFunctor(..)
, (<$$>)
  -- ** Higher-order fixed points and folds
, HFix(..)
, hcata
, hcataM
  -- * Important HFunctors
, HSum(..)
, HProduct(..)
, HCompose(..)
, Promoted(..)
  -- * Higher-order generic traversals
, HTraversable(..)
  -- * Higher-order equality
, HEq(..)
  -- * Miscellaneous
, rewrite
  -- * Reexports
, Compose(..)
) where

import Data.Function ( on )
import Data.Functor.Compose

-- | The class of polykinded higher-order functors.
--
-- Whereas a simple functor can be thought of as a context around a value, a
-- higher-order functor can be thought of as a context around another functor.
--
-- Any regular 'Functor' can be made an instance of HFunctor by choosing
-- @k ~ ()@, since @() -> *@ is isomorphic to @*@.
class HFunctor (h :: (k -> *) -> k -> *) where
  -- | A higher-order 'fmap'. By contrast with the simple @fmap@ which lifts
  -- simple functions into functions operating in the Functor, hfmap lifts
  -- natural transformations between functors into natural transformations
  -- operating in the HFunctor.
  hfmap :: (f :~> g) -> h f :~> h g

infixl 4 <$$>
(<$$>) :: HFunctor h => (f :~> g) -> h f :~> h g
(<$$>) = hfmap

-- | for any functor @f@, @Promoted f@ represents its representation as a
-- higher-order functor.
newtype Promoted (f :: * -> *) (uf :: () -> *) (u :: ())
  = Promoted
    { unPromoted :: f (uf u)
    }

instance Functor f => HFunctor (Promoted f) where
  hfmap nat (Promoted x) = Promoted (nat <$> x)

-- | Natural transformations.
--
-- Intuitively, a natural transformation between functors is a uniform
-- transformation of the context around the value. By \"uniform\", it is
-- understood that the transformation can in no way examine the value in order
-- to perform the transformation.
--
-- This is enforced on the type level by using parametricity.
type f :~> g = forall a. f a -> g a

-- | The fixed point of a higher order functor.
newtype HFix (h :: (k -> *) -> k -> *) (a :: k)
  = HFix { unHFix :: h (HFix h) a }

infix 4 ===

-- | Higher-order equality.
class HEq (f :: k -> *) where
  (===) :: f a -> f a -> Bool

-- | We can check equality of a higher-order fixed point if we can check the
-- equality of its unfolding.
--
-- /Undecidable ?/
instance HEq (f (HFix f)) => HEq (HFix f) where
  (===) = (===) `on` unHFix

instance HEq (f :: k -> *) => HEq (Compose [] f) where
  Compose [] === Compose [] = False
  Compose [] === Compose (_:_) = False
  Compose (_:_) === Compose [] = False
  Compose (x:xs) === Compose (y:ys) = x === y && Compose xs === Compose ys

instance HEq (f :: k -> *) => HEq (Compose Maybe f) where
  Compose Nothing === Compose Nothing = True
  Compose (Just _) === Compose Nothing = False
  Compose Nothing === Compose (Just _) = False
  Compose (Just x) === Compose (Just y) = x === y

-- | Higher-order catamorphism.
--
-- Folds a higher-order functor fixpoint into a functor in a bottom-up fashion.
hcata
  :: forall (h :: (k -> *) -> k -> *) (f :: k -> *) (a :: k). HFunctor h
  => (forall (b :: k). h f b -> f b)
  -> HFix h a -> f a
hcata hAlg = hAlg . hfmap (hcata hAlg) . unHFix

-- | Optional tree rewriting strategy.
--
-- Allows the programmer to use strategies that can choose to leave a subtree
-- as-is by returning 'Nothing'. In that case, the input subtree is used.
rewrite
  :: (forall (b :: k). h (HFix h) b -> Maybe (h (HFix h) b))
  -> h (HFix h) a
  -> h (HFix h) a
rewrite phi s = maybe s id (phi s)

-- | Monadic higher-order catamorphism.
--
-- Folds a higher-order functor fixpoint into a functor in a bottom-up fashion,
-- performing side effects top-down, left-to-right.
hcataM
  :: forall (h :: (k -> *) -> k -> *) (f :: k -> *) (m :: * -> *) (a :: k).
    (Monad m, HTraversable h)
  => (forall (b :: k). h f b -> m (f b))
  -> HFix h a
  -> m (f a)
hcataM hAlgM = (>>= hAlgM) . traverseH (hcataM hAlgM) . unHFix

-- | Product HFunctor.
--
-- We have left and right projections to extract the relevant HFunctor.
data HProduct h1 h2 f a
  = P
    { left :: h1 f a
    , right :: h2 f a
    }

instance (HFunctor h1, HFunctor h2) => HFunctor (HProduct h1 h2) where
  hfmap phi (P l r) = P (hfmap phi l) (hfmap phi r)

-- | Sum HFunctor.
--
-- We have left and right branches to choose between two HFunctors.
data HSum h1 h2 f a = L (h1 f a) | R (h2 f a)

instance (HFunctor h1, HFunctor h2) => HFunctor (HSum h1 h2) where
  hfmap phi s = case s of
    L h -> L (hfmap phi h)
    R h -> R (hfmap phi h)

-- | Composed HFunctor.
--
-- An HFunctor surrounding another HFunctor is still an HFunctor.
newtype HCompose h1 h2 f a
  = HC
    { hc :: h1 (h2 f) a
    }

instance (HFunctor h1, HFunctor h2) => HFunctor (HCompose h1 h2) where
  hfmap phi (HC h) = HC $ hfmap (hfmap phi) h

-- | Class of higher-order functors whose side-effects can be sequenced
-- left-to-right.
class HFunctor h => HTraversable (h :: (k -> *) -> k -> *) where
  -- | If a higher-order functor contains side effects in its recursive
  -- positions, then they can be sequenced left-to-right, hoisting the actions
  -- up.
  --
  -- Generalizes
  -- @sequenceA :: (Traversable t, Applicative f) => t (f a) -> f (t a)@.
  sequenceH :: Applicative m => h (Compose m f) a -> m (h f a)

  -- | Transform the functors inside the higher-order functor by performing
  -- effects. Evaluate the effects from left to right and collect the results.
  --
  -- Generalizes
  -- @traverse :: (Traversable t, Applicative f) => (a -> f b) -> t a -> f (t b)@.
  traverseH
    :: Applicative m
    => (forall (b :: k). f b -> m (g b))
    -> h f a
    -> m (h g a)
  traverseH f = sequenceH . hfmap (Compose . f)
