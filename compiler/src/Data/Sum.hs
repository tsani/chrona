module Data.Sum where

data S (ps :: [k -> *]) (a :: k) :: * where
  SHere :: p a -> S ps a -> S (p ': ps) a
  SThere :: S ps a -> S (p ': ps) a

data Elim (ps :: [k -> *]) (rs :: [k -> *]) (a :: k) :: * where
  Done :: Elim '[] '[] a
  Case :: (p a -> r a) -> Elim ps rs -> Elim (p ': ps) (r ': rs) a
