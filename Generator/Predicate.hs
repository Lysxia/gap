{-# LANGUAGE DeriveFunctor #-}

module Generator.Predicate where

import Data.Profunctor
import Test.QuickCheck

class Profunctor p => Property p where

newtype Predicate x a
  = Predicate { applyPredicate :: x -> Maybe a }
  deriving Functor

instance Profunctor Predicate where
  rmap = fmap
  lmap f (Predicate p) = Predicate (p . f)

newtype Generator x a
  = Generator { runGenerator :: Gen (Maybe a) }
  deriving Functor

instance Profunctor Generator where
  rmap = fmap
  lmap _ (Generator g) = Generator g
