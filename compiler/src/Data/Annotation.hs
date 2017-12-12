{-|
Module      : Data.Annotation
Description : Indexed annotations for higher-order functors
Copyright   : (c) Jacob Errington 2017
License     : MIT
Maintainer  : chrona@mail.jerrington.me
Stability   : experimental

Indexed annotations for higher-order functors.
-}

module Data.Annotation
( -- * Indexed annotations on higher-order functors
  IAnn(..)
, IAnnFix
, FixAnn
, stripAnn
, topAnn
, mapTopAnn
  -- ** Combinators
, reannotate
, reannotateTree
, reannotateM
, singleton
, unsingleton
, consAnnotate
, consAnnotateM
, topDownConsAnnotate
, topDownConsAnnotateM
-- , reannotateHeadM
  -- * Crazy stuff
, P(..)
, PAnn
, (|:|)
, PElem(..)
  -- * Reexports
, Proxy(..)
) where

import Data.HFunctor
import Data.HFunctor.Basic ( (<&>) )
import Data.HFunctor.TopDown

import Data.Proxy

-- | Indexed annotations for higher-order functors.
--
-- * @p@ -- the type-level function that interprets the index into a concrete
--   type.
-- * @h@ -- the higher-order functor
-- * @f@ -- the functor that the hfunctor provides context to
-- * @a@ -- the index
--
-- The reason we require so many type parameters is that for a fixed
-- interpretation @p@, @IAnn p h@ can be given an HFunctor instance provided
-- @h@ is an HFunctor.
--
-- By using a type-level function @p@ to interpret the index, we can have
-- different types of annotations on different parts of the syntax tree,
-- discriminated by their index.
data IAnn
  (p :: k -> *)
  (h :: (k -> *) -> k -> *)
  (f :: k -> *)
  (a :: k)
  = IAnn
    { ann :: !(p a)
    -- ^ The annotation, whose type is determined by the index interpretation
    -- on the index.
    , bare :: h f a
    -- ^ The annotated data.
    }

instance HFunctor h => HFunctor (IAnn x h) where
  hfmap f (IAnn a h) = IAnn a (hfmap f h)

instance HTraversable h => HTraversable (IAnn p h) where
  sequenceH (IAnn a node) = IAnn <$> pure a <*> sequenceH node

-- | The fixpoint of an indexed-annotated higher-order functor.
type IAnnFix p h = IAnn p h (HFix (IAnn p h))

type FixAnn p h = HFix (IAnn p h)


-- | A nicer way to represent a whole bunch of separate annotations, as a
-- type-indexed list.
data P (ps :: [k -> *]) (a :: k) :: * where
  PNil :: P '[] a
  PCons :: p a -> P ps a -> P (p ': ps) a

type PAnn (ps :: [k -> *]) = IAnn (P ps)

(|:|) :: p a -> P ps a -> P (p ': ps) a
(|:|) = PCons

singleton :: p a -> P '[p] a
singleton x = x |:| PNil

unsingleton :: P '[p] a -> p a
unsingleton (PCons x PNil) = x

-- | Used to access annotations inside a list.
class PElem
  (i :: k -> *)
  (p :: [k -> *] -> k -> *)
  (ps :: [k -> *]) where
    getH :: Proxy i -> p ps a -> i a

instance {-# OVERLAPPING #-} (p' ~ P) => PElem p p' (p ': hs) where
  getH _ (PCons x _) = x

instance (p' ~ P, PElem p p' ps) => PElem p p' (q ': ps) where
  getH p (PCons _ xs) = getH p xs

-- | Extract the annotation at the root of the tree.
topAnn :: FixAnn p h a -> p a
topAnn (HFix (IAnn a _)) = a

-- | Apply a function to the annotation at the root of the tree.
mapTopAnn :: (p a -> p a) -> FixAnn p h a -> FixAnn p h a
mapTopAnn f (HFix (IAnn a s)) = HFix (IAnn (f a) s)

-- | Remove all annotations from an indexed-annotated syntax tree.
stripAnn :: HFunctor h => FixAnn p h i -> HFix h i
stripAnn = hcata (HFix . bare)

-- | Combinator for rewriting annotations.
-- If a tree is annotated with @p@, then reannotate lets you view the node
-- @h f a@ that is annotated along with its annotation @p a@ and transform the
-- annotation into a new one @q a@.
--
-- If you don't care about the node and just want to rewrite the annotation,
-- then use @reannotate (const f)@.
reannotate
  :: forall (h :: (k -> *) -> k -> *) (p :: k -> *) (q :: k -> *) (f :: k -> *).
    (forall (a :: k). h f a -> p a -> q a)
  -> IAnn p h f :~> IAnn q h f
reannotate f (IAnn a node) = IAnn (f node a) node

-- | Adds a new annotation to a list of annotations.
consAnnotate
  :: forall (h :: (k -> *) -> k -> *) (ps :: [k -> *]) (p :: k -> *) (f :: k -> *).
    (forall (a :: k). h f a -> P ps a -> p a)
  -> (forall (a :: k). IAnn (P ps) h f a -> IAnn (P (p ': ps)) h f a)
consAnnotate f (IAnn a node) = IAnn (f node a |:| a) node

consAnnotateM
  :: forall
    (m :: * -> *)
    (h :: (k -> *) -> k -> *)
    (ps :: [k -> *])
    (p :: k -> *)
    (f :: k -> *).
    Applicative m
  => (forall (a :: k). h f a -> P ps a -> m (p a))
  -> (forall (a :: k). PAnn ps h f a -> m (PAnn (p ': ps) h f a))
consAnnotateM f (IAnn a node) =
  IAnn <$> ((|:|) <$> f node a <*> pure a) <*> pure node

-- consAnnotateMTD
--   :: forall
--     (m :: * -> *)
--     (r :: k -> *)
--     (h :: (k -> *) -> k -> *)
--     (ps :: [k -> *])
--     (p :: k -> *)
--     (f :: k -> *).
--     Applicative m
--   => (forall (a :: k). h (TopDown r f) a -> P ps a -> m (TopDown r f)

-- | Rewrite the annotations on a whole tree.
reannotateTree
  :: HFunctor h
  => (forall b. h (HFix (IAnn q h)) b -> p b -> q b)
  -> FixAnn p h a
  -> FixAnn q h a
reannotateTree f = hcata (HFix . reannotate f)

-- | Combinator for rewriting annotations monadically.
--
-- This saves you the trouble of having to reconstruct each node manually and
-- from having to use newtype tricks to do the same thing using 'reannotate'.
reannotateM
  :: forall
    (m :: * -> *)
    (h :: (k -> *) -> k -> *)
    (p :: k -> *)
    (q :: k -> *)
    (f :: k -> *).
    Applicative m
  => (forall (a :: k). h f a -> p a -> m (q a))
  -> (forall (a :: k). IAnn p h f a -> m (IAnn q h f a))
reannotateM f (IAnn a node) = IAnn <$> (f node a) <*> pure node

-- reannotateHeadM
--   :: forall
--     (m :: * -> *)
--     (h :: (k -> *) -> k -> *)
--     (p :: k -> *)
--     (q :: k -> *)
--     (ps :: [k -> *])
--     (f :: k -> *).
--     Applicative m
--   => (forall (a :: k). h f a -> p a -> m (q a))
--   -> (forall (a :: k). PAnn (p ': ps) h f a -> m (PAnn (q ': ps) h f a))
-- reannotateHeadM phi = reannotateM phi' where
--   phi' :: forall (a :: k). h f a ->
--   phi' node (PCons p ps) = PCons <$> phi node p <*> ps

-- reannotateTreeM
--   :: forall
--     (m :: * -> *)
--     (h :: (k -> *) -> k -> *)
--     (p :: k -> *)
--     (q :: k -> *)
--     (f :: k -> *)
--     (a :: k).
--     (Monad m, HTraversable h)
--   => (forall (a :: k). h f a -> p a -> m (q a))
--   -> IAnnFix p h a
--   -> m (IAnnFix q h a)
-- reannotateTreeM p = hcataM (fmap HFix . reannotateM p)

topDownConsAnnotateM
  :: forall
    (n :: * -> *)
    (m :: * -> *)
    (h :: (k -> *) -> k -> *)
    (ps :: [k -> *])
    (p :: k -> *)
    (t :: k -> *)
    (f :: k -> *).
    (Applicative m, Functor n)
  => (
    forall (a :: k).
    h (TopDownHT t n f) a -> P ps a -> m (ReaderT (t a) n (p a, h f a))
  )
  -> (
    forall (a :: k).
    PAnn ps h (TopDownHT t n f) a -> m (TopDownHT t n (PAnn (p ': ps) h f) a)
  )
topDownConsAnnotateM phi (IAnn ps node) = do
  f <- phi node ps
  pure (TopDownHT $ \r -> f $$ r <&> \(p, node') -> IAnn (p |:| ps) node')

topDownConsAnnotate
  :: forall
    (m :: * -> *)
    (h :: (k -> *) -> k -> *)
    (ps :: [k -> *])
    (p :: k -> *)
    (t :: k -> *)
    (f :: k -> *).
    Functor m
  => (
    forall (a :: k).
    h (TopDownHT t m f) a -> P ps a -> ReaderT (t a) m (p a, h f a)
  )
  -> (
    forall (a :: k).
    PAnn ps h (TopDownHT t m f) a -> TopDownHT t m (PAnn (p ': ps) h f) a
  )
topDownConsAnnotate phi (IAnn ps node) =
  TopDownHT $ \r -> (phi node ps) $$ r <&> \(p , node') -> IAnn (p |:| ps) node'

