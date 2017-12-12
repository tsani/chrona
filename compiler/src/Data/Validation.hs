module Data.Validation where

import Data.HFunctor

import Data.Monoid ( (<>) )

-- | Same as 'Sum', but does not provide a 'HMonad' instance, instead using
-- an 'HApplicative' to collect all failures.
data Validation (e :: *) (f :: k -> *) (a :: k)
  = Failure e
  | Success (f a)

instance HFunctor (Validation e) where
  hfmap phi s = case s of
    Failure x -> Failure x
    Success x -> Success (phi x)

instance Monoid e => HApplicative (Validation e) where
  hpure x = Success x
  Success (Nat' f) <**> Success x = Success (f x)
  Success _ <**> Failure e = Failure e
  Failure e <**> Success _ = Failure e
  Failure e1 <**> Failure e2 = Failure (e1 <> e2)
