module Data.HFunctor.Basic
( -- * Basic polykinded functors
  K(..)
, I(..)
, repackage, kmap
  -- * Syntax
, (<&>)
) where

(<&>) :: Functor f => f a -> (a -> b) -> f b
(<&>) = flip fmap

-- | Constant functor.
--
-- Can be considered a type-level constant function.
--
-- The @fmap@ implementation simply ignores the given function, and rewrites
-- the type.
newtype K x (a :: k) = K { unK :: x } deriving Functor

kmap :: (x -> y) -> K x a -> K y b
kmap f (K x) = K (f x)

-- | Rewrite the type of a constant functor.
repackage :: K x a -> K x b
repackage = kmap id

-- | Identity functor. This is just a box around a value.
--
-- The @fmap@ implementation simply applies the function to the boxed value.
newtype I a = I { unI :: a } deriving Functor
