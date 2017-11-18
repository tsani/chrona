module Data.HFunctor.TopDown
( -- * Top-down traversal
  TopDownHT(..)
, TopDownH
, UTopDownH
  -- * Conversion to @ReaderT@
, toReaderT, fromReaderT
  -- * Reexports
, ($$)
, ReaderT(..)
, Reader
, withReaderT, local, ask, asks
, Identity(..)
) where

import Data.Apply
import Data.HFunctor ( HFunctor(..) )
import Data.HFunctor.Basic

import Control.Monad.Trans.Reader
import Data.Coerce ( coerce )
import Data.Functor.Identity ( Identity(..) )

-- | This is a combination of 'HCompose' and the arrow functor @(->) r@ that
-- gives rise to the @Reader@ monad.
--
-- This functor can be used in rebuilding the tree when information needs to
-- flow top-down: when putting the node back together in a tree rebuilding,
-- each subtree will be represented as @UTopDown r f n@ where for a rebuilding
-- @f ~ HFix h@ for the 'HFunctor' @h@ that the tree is build from.
-- It suffices to access to @r@ that comes from above, adjust it if necessary,
-- and use that modified @r@ to compute the subtrees.
-- This produces a top-down flow of data.
--
-- The top-down flow given by this data type is /uniform/ in contrast to
-- 'TopDown' which gives an indexed flow: the input type for subtrees can
-- differ according to their index.
type UTopDownH r f a = TopDownH (K r) f a

-- | Top-down information flow in a traversal with indexed dataflow.
--
-- See 'UTopDownH' for perspective.
type TopDownH (r :: k -> *) (f :: k -> *) (a :: k) = TopDownHT r Identity f a

-- | A top-down information flow as a monad transformer.
--
-- This isn't really a monad transformer since it's a higher-order functor, but
-- it can be converted to and from 'ReaderT' provided that the indices line up
-- correctly.
newtype TopDownHT (r :: k -> *) (m :: * -> *) (f :: k -> *) (a :: k)
  = TopDownHT
    { topDownT' :: r a -> m (f a)
    }

toReaderT :: TopDownHT r m f a -> ReaderT (r a) m (f a)
toReaderT = coerce
{-# INLINE toReaderT #-}

fromReaderT :: ReaderT (r a) m (f a) -> TopDownHT r m f a
fromReaderT = coerce
{-# INLINE fromReaderT #-}

instance Functor m => HFunctor (TopDownHT r m) where
  hfmap nat f = TopDownHT $ \r -> fmap nat (f $$ r)

instance Apply (TopDownHT r m f a) where
  type Input (TopDownHT r m f a) = r a
  type Output (TopDownHT r m f a) = m (f a)
  apply (TopDownHT f) x = f x
