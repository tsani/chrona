module Data.Profunctor where

class Profunctor p where
  dimap :: (a -> b) -> (s -> t) -> p b s -> p a t
  dimap f g = lmap f . rmap g

  lmap :: (a -> b) -> p b s -> p a s
  lmap f = dimap f id

  rmap :: (s -> t) -> p a s -> p a t
  rmap g = dimap id g
