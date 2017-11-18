module Data.Apply
( Apply(..)
, ($$)
) where

import Control.Monad.Trans.Reader

-- | Things that behave like functions.
class Apply f where
  type Input f :: *
  type Output f :: *
  apply :: f -> Input f -> Output f

($$) :: Apply f => f -> Input f -> Output f
($$) = apply
infixl 9 $$

instance Apply (ReaderT r m a) where
  type Input (ReaderT r m a) = r
  type Output (ReaderT r m a) = m a
  apply (ReaderT f) x = f x
