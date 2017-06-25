{-# LANGUAGE DeriveFunctor #-}

{- |

For a generator @g :: Gen a@ and a predicate @p :: a -> Bool@.

We write @x ∈ g@ if @g@ generates @x@ with positive probability.

@
p x = True   ==>   x ∈ g   (completeness of g wrt. p)
x ∈ g   ==>   p x = True   (soundness)
@

We have an abstract type @p :: * -> * -> *@, whose values @g :: p x a@
represent a generator @runGenerator g :: Gen a@ and a partial function
@runPredicate g :: x -> Maybe a@ (which corresponds to a predicate).

Properties we want to have are:

1. If @runPredicate g x = Just a@, then @a ∈ runGenerator g@.
2. If @a ∈ runGenerator g@, then there exists @x@ such that @runPredicate g x = Just a@.
3. If @runPredicate g x = Just a@, then @x = a@.

(1+3) describes completeness, (2+3) soundness.

-}

module Generator.Predicate where

import Control.Applicative
import Control.Monad
import Data.Functor
import Data.Maybe
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

  -- | > integer r  -- @0 < r < 1@
  --
  -- - Predicate: Pass through.
  -- - Generator: Geometric distribution then
  --   @\n -> if even n then n `div` 2 else (-n) `div` 2@.
  integer :: Double -> p Int Int

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
  = Predicate { runPredicate :: x -> Maybe a }
  deriving Functor

applyPredicate :: Predicate x a -> x -> Bool
applyPredicate p = isJust . runPredicate p

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
    runPredicate (k a) x)

instance Properties Predicate where
  inRange (inf, sup) = predicate (\a -> inf <= a && a <= sup)
  bernoulli _ = true
  integer _ = true
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
  integer p = generator (do
    x <- geometric p
    return $
      if even x then
        x `div` 2
      else
        (-x) `div` 2)
  nonNegative p = generator (geometric p)
  finite = Generator . frequency . (fmap . fmap) (pure . pure)

geometric :: Double -> Gen Int
geometric p = g 0
    where
      g n = do
        x <- choose (0, 1)
        if x < p then
          return n
        else
          g $! n+1

newtype Shrinker x a
  = Shrinker { runShrinker :: x -> [a] }
  deriving Functor

shrinks :: (a -> [a]) -> Shrinker a a
shrinks s = Shrinker (\a -> a : s a)

instance Profunctor Shrinker where
  rmap = fmap
  lmap f (Shrinker s) = Shrinker (s . f)

instance Applicative (Shrinker x) where
  pure a = Shrinker (\_ -> [a])
  Shrinker sf <*> Shrinker sa = Shrinker (\x ->
    case (sf x, sa x) of
      (f : fs, a : as) -> f a : fmap ($ a) fs ++ fmap f as
      _ -> [])

instance Alternative (Shrinker x) where
  empty = Shrinker (\_ -> [])
  Shrinker sa <|> Shrinker sa' = Shrinker (\x ->
    case sa x of
      [] -> sa' x
      as -> as)

instance Monad (Shrinker x) where
  Shrinker sa >>= k = Shrinker (\x ->
    case sa x of
      [] -> []
      a : as -> case runShrinker (k a) x of
        [] -> []
        bs -> bs ++ do
          a <- as
          take 1 (runShrinker (k a) x))

instance Properties Shrinker where
  inRange (inf, sup) = Shrinker (\a ->
    if a < inf || a > sup then
      []
    else if a == inf || a == sup then
      a : []
    else
      a : [(inf + a) `div` 2, (sup + a) `div` 2 + 1, a - 1, a + 1])
  bernoulli _ = shrinks (\a -> if a then [False] else [])
  integer _ = shrinks (\a -> case compare a 0 of
    GT -> [a `quot` 2, a - 1]
    EQ -> []
    LT -> [a `quot` 2, a + 1])
  nonNegative _ = Shrinker (\a ->
    if a < 0 then
      []
    else
      a : [a `div` 2, a - 1])
  finite _ = Shrinker maybeToList
