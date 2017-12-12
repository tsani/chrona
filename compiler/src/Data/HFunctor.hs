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
, HApplicative(..)
, HMonad(..)
, (<$$>)
  -- ** Higher-order fixed points and folds
, HFix(..)
, hcata
, hcataM
  -- * Important (H)Functors
, I(..)
, K(..)
, Sum(..)
, HSum(..)
, HProduct(..)
, HCompose(..)
, Promoted(..)
, Nat (..)
, Nat' (..)
  -- * Higher-order generic traversals
, HTraversable(..)
, TraversableH(..)
  -- * Higher-order equality
, HEq(..)
  -- * Higher-order monoids
, HMonoid(..)
  -- * Miscellaneous
, rewrite
  -- * Reexports
, Compose(..)
, (<&>)
, (&)
) where

import Data.Apply
import Data.HFunctor.Basic

import Data.Monoid ( (<>) )
import Data.Function ( on )
import Data.Functor.Compose

-- | The class of polykinded higher-order functors.
--
-- Whereas a simple functor can be thought of as a context around a value, a
-- higher-order functor can be thought of as a context around another functor.
--
-- Any regular 'Functor' can be made an instance of HFunctor by choosing
-- @k ~ ()@, since @() -> *@ is isomorphic to @*@.
-- 'Promoted' shows that this is true.
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
  hfmap phi (Promoted x) = Promoted (phi <$> x)

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
data HSum h1 h2 f a = HL (h1 f a) | HR (h2 f a)

instance (HFunctor h1, HFunctor h2) => HFunctor (HSum h1 h2) where
  hfmap phi s = case s of
    HL h -> HL (hfmap phi h)
    HR h -> HR (hfmap phi h)

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

  -- Not generally implementable!
  -- htraverse
  --   :: HApplicative j
  --   => (forall (b :: k). f b -> j g b)
  --   -> h f a
  --   -> j (h g) a

-- but we _can_ implement a special case for lists.
-- hsequence :: HApplicative j => [j g a] -> j (Compose [] g) a
-- hsequence [] = hpure $ Compose []
-- hsequence (x:xs) = (hpure phi) <**> x <**> hsequence xs where
--   phi :: Nat' g a (Nat' (Compose [] g) a (Compose [] g)) a
--   phi = Nat' $ \x' -> Nat' $ \(Compose xs') -> Compose (x' : xs')

-- traverse :: (a -> f b) -> t a -> f (t a)

class TraversableH t where
  htraverse
    :: HApplicative h
    => (f :~> h g)
    -> t (f a)
    -> h (Compose t g) a

  hsequence
    :: HApplicative h
    => t (h f a)
    -> h (Compose t f) a

instance TraversableH [] where
  htraverse _ [] = hpure (Compose [])
  htraverse phi (x:xs) = hpure f <**> phi x <**> htraverse phi xs where
    f = Nat' $ \x' -> Nat' $ \(Compose xs') -> Compose (x' : xs')

  hsequence [] = hpure $ Compose []
  hsequence (x:xs) = (hpure phi) <**> x <**> hsequence xs where
    phi = Nat' $ \x' -> Nat' $ \(Compose xs') -> Compose (x' : xs')

instance TraversableH Maybe where
  htraverse _ Nothing = hpure (Compose Nothing)
  htraverse phi (Just x) = hpure f <**> phi x where
    f :: Nat' g a (Compose Maybe g) a
    f = Nat' $ \x' -> Compose (Just x')

  hsequence Nothing = hpure (Compose Nothing)
  hsequence (Just x) = hpure f <**> x where
    f = Nat' $ \x' -> Compose (Just x')


-- | A natural transformation that we can partially apply.
newtype Nat (f :: k -> *) (g :: k -> *) (a :: k)
  = Nat { nat :: f a -> g a }

instance Apply (Nat f g a) where
  type Input (Nat f g a) = f a
  type Output (Nat f g a) = g a
  apply (Nat f) x = f x

instance HFunctor (Nat f) where
  hfmap phi (Nat psi) = Nat (phi . psi)

newtype Nat' (f :: k -> *) (b :: k) (g :: k -> *) (a :: k)
  = Nat' { nat' :: f b -> g a }

instance HFunctor (Nat' f b) where
  hfmap phi (Nat' psi) = Nat' (phi . psi)

instance HApplicative (Nat' f c) where
  hpure x = Nat' $ \_ -> x
  Nat' phi <**> Nat' x = Nat' $ \z ->
    let x' = x z
        (Nat' y) = phi z
        in y x'

class HMonoid (f :: k -> *) where
  hempty :: f a
  (<^>) :: f a -> f a -> f a

-- | Any monoid can be promoted to a HMonoid using a constant.
instance Monoid x => HMonoid (K x) where
  hempty = K mempty
  K x <^> K y = K (x <> y)

class HFunctor h => HApplicative h where
  hpure :: f a -> h f a
  (<**>) :: h (Nat' f a g) b -> h f a -> h g b

class HApplicative h => HMonad h where
  (>^>=) :: h f a -> (f :~> h g) -> h g a

data Sum (f :: k -> *) (a :: k) (g :: k -> *) (b :: k)
  = L (f a)
  | R (g b)

instance HFunctor (Sum g a) where
  hfmap phi (R x) = R (phi x)
  hfmap _ (L x) = L x

instance HApplicative (Sum g a) where
  hpure = R
  R (Nat' f) <**> R x = R (f x)
  L x <**> _ = L x
  _ <**> L x = L x

(&) :: a -> (a -> b) -> b
(&) = flip ($)
infixr 0 &
