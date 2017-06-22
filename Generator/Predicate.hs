{-# LANGUAGE DeriveFunctor #-}

module Generator.Predicate where

import Control.Applicative
import Control.Monad
import Data.Functor
import Data.Profunctor
import Test.QuickCheck

class Profunctor p => Properties p where
  -- | Inclusive range.
  --
  -- - Predicate: Assert that the input 'Int' is within the given range.
  -- - Generator: Generate an 'Int' in the given range, with uniform distribution.
  inRange :: (Int, Int) -> p Int Int

  -- | > bernoulli r  -- @0 < r < 1@
  --
  -- - Predicate: Pass through.
  -- - Generator: Generate a boolean, 'True' with probability @r@, 'False' with
  --   probability @1-r@.
  bernoulli :: Double -> p Bool Bool

  -- | > nonNegative r  -- @0 < r < 1@
  --
  -- - Predicate: Non-negative integers (@>= 0@).
  -- - Generator: Geometric distribution.
  nonNegative :: Double -> p Int Int

  -- | Finite set.
  --
  -- - Predicate: Unwrap a @Just@. Fail on @Nothing@.
  -- - Generator: Choose an element with probability proportional to its weight.
  finite :: [(Int, a)] -> p (Maybe a) a

newtype Predicate x a
  = Predicate { applyPredicate :: x -> Maybe a }
  deriving Functor

predicate :: (a -> Bool) -> Predicate a a
predicate f = Predicate $ \a -> guard (f a) $> a

true :: Predicate a a
true = Predicate (\a -> Just a)

instance Profunctor Predicate where
  rmap = fmap
  lmap f (Predicate p) = Predicate (p . f)

instance Applicative (Predicate x) where
  pure a = Predicate (\_ -> Just a)
  Predicate pf <*> Predicate pa = Predicate (liftA2 (<*>) pf pa)

instance Alternative (Predicate x) where
  empty = Predicate (\_ -> Nothing)
  Predicate pa <|> Predicate pa' = Predicate (liftA2 (<|>) pa pa')

instance Monad (Predicate a) where
  Predicate pa >>= k = Predicate (\x -> do
    a <- pa x
    applyPredicate (k a) x)

instance Properties Predicate where
  inRange (inf, sup) = predicate (\a -> inf <= a && a <= sup)
  bernoulli _ = true
  nonNegative _ = predicate (>= 0)
  finite _ = Predicate id

newtype Generator x a
  = Generator { runGenerator :: Gen (Maybe a) }
  deriving Functor

generator :: Gen a -> Generator x a
generator g = Generator (fmap Just g)

instance Profunctor Generator where
  rmap = fmap
  lmap _ (Generator g) = Generator g

instance Applicative (Generator x) where
  pure a = Generator (pure (Just a))
  Generator gf <*> Generator ga = Generator (liftA2 (<*>) gf ga)

instance Alternative (Generator x) where
  empty = Generator (pure Nothing)
  Generator ga <|> Generator ga' = Generator (liftA2 (<|>) ga ga')

instance Monad (Generator x) where
  Generator ga >>= k = Generator (do
    a_ <- ga
    case a_ of
      Just a -> runGenerator (k a)
      Nothing -> pure Nothing)

instance Properties Generator where
  inRange (inf, sup) = generator (choose (inf, sup))
  bernoulli p = generator (do
    x <- choose (0, 1)
    return (x < p))
  nonNegative p = generator (g 0)
    where
      g n = do
        x <- choose (0, 1)
        if x < p then
          return n
        else
          g $! n+1
  finite = Generator . frequency . (fmap . fmap) (pure . pure)
