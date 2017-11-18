{-|
Module      : Data.Reflection
Description : Type-level tricks for reflecting types into values
Copyright   : (c) Jacob Errington 2017
License     : MIT
Maintainer  : chrona@mail.jerrington.me
Stability   : experimental

In Haskell, you can't pattern match on types... unless you import this module.

Two different varieties of reflection are available in this module.

 * 'ReflectS' allows you to reflect types into values /indexed by/ the
    original type.

For more information on this trick, see \"/Dependently Typed Programming with
Singletons/, published at the Haskell Symposium, 2012\".
-}

{-# LANGUAGE TypeInType #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Reflection
(
  -- * Reflection
  Reflect(..)
, Demote
  -- * Existential types
, Witness
, Exists(..)
, Forget(..)
  -- ** Existential for reflection
, Reflectable
, Witnessing(..)
  -- * Polykinded equality
, PolyEq(..)
, (=*=)
  -- * Reexports
, KProxy(..)
, Proxy(..)
) where

import Data.Kind
import Data.Proxy

class PolyEq (p :: k -> *) where
  peq :: p n -> p m -> Bool

  pneq :: p n -> p m -> Bool
  pneq p1 p2 = not $ peq p1 p2

(=*=) :: PolyEq p => p n -> p m -> Bool
(=*=) = peq

-- | Type-level function that converts a kind (represented as a type by a
-- proxy) into type constructor taking types from that kind to types.
type family Demote k :: k -> *

-- | Class of types that can be reflected to indexed values.
--
-- This effectively allows you to pattern match on types, using singletons as
-- the actual objects to match on.
--
-- Use ScopedTypeVariables to construct the proxy object corresponding to the
-- type you want to match on, and this method synthesizes its corresponding
-- singleton.
class Reflect (a :: k) where
  reflect :: Proxy (a :: k) -> Demote k a

data Box (a :: *) :: * where
  Box :: a -> Box a

deriving instance Functor Box

-- | Witnesses for different kinds.
--
-- A witness for a type of kind @*@ is a value (held in a 'Box').
-- A witness for a type in any other kind is a proxy, since these other types
-- don't have values.
type family Witness k :: k -> * where
  Witness Type = Box
  Witness _ = Proxy

data Exists (c :: a -> Constraint) k where
  Some :: forall c (a :: k). c a => Witness k a -> Exists c k

class Forget (p :: k -> *) where
  forget :: forall (a :: k). p a -> Exists Reflect k

-- | Store a witness along with a proposition.
-- The witness should be a singleton so that matching on it always reveals what
-- the index @a@ is. This then informs what cases exist for @q@.
data Witnessing (p :: k -> *) (q :: k -> *) where
  Witnessing :: p a -> q a -> Witnessing p q

type Reflectable = Exists Reflect

-- /Undecidable/ due to the 'PolyEq' constraint on the reflected value involving
-- the variable @k@!
--
-- To avoid making the typechecker hang, ensure that any 'PolyEq'
-- implementations do not use the @Eq@ instance for 'Reflectable'.
instance (PolyEq (Demote k), Witness k ~ Proxy) => Eq (Exists Reflect k) where
  (==) (Some (p1 :: Proxy a)) (Some (p2 :: Proxy b)) = reflect p1 =*= reflect p2
