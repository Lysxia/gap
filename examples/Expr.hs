{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImplicitParams #-}

{-# OPTIONS -Wno-missing-fields -Wno-missing-methods #-}

module Expr where

import Control.Applicative
import Data.Foldable
import Data.Maybe
import GHC.Generics

import Test.QuickCheck
import Generator.Predicate
import Profunctor.Monad

data Expr
  = If { cond :: Expr, branch1 :: Expr, branch2 :: Expr}
  | Plus { operand1 :: Expr, operand2 :: Expr }
  | Equal { operand1 :: Expr, operand2 :: Expr }
  | And { operand1 :: Expr, operand2 :: Expr }
  | Not { unNot :: Expr }
  | Var { unVar :: Var }
  | CInt { unCInt :: Int }
  | CBool { unCBool :: Bool }
  deriving (Generic, Show)

type Var = Int

data Type = TBool | TInt
  deriving (Eq, Show)

assert :: Bool -> String -> Either String ()
assert True _ = Right ()
assert False e = Left e

typeOf :: Expr -> Either String Type
typeOf e = case e of
  If e1 e2 e3 -> do
    [t1, t2, t3] <- traverse typeOf [e1, e2, e3]
    assert (t1 == TBool) "Non-boolean condition"
    assert (t2 == t3) "Mismatched branches"
    return t2
  Plus e1 e2 -> do
    [t1, t2] <- traverse typeOf [e1, e2]
    assert (t1 == TInt && t2 == TInt) "Int addition"
    return TInt
  Equal e1 e2 -> do
    [t1, t2] <- traverse typeOf [e1, e2]
    assert (t1 == TInt && t2 == TInt) "Compare Int"
    return TBool
  And e1 e2 -> do
    [t1, t2] <- traverse typeOf [e1, e2]
    assert (t1 == TBool && t2 == TBool) "And bool"
    return TBool
  Not e1 -> do
    t1 <- typeOf e1
    assert (t1 == TBool) "Not Bool"
    return TBool
  Var _ -> return TInt
  CInt _ -> return TInt
  CBool _ -> return TBool

genInt :: Gen Expr
genInt = sized $ \n -> oneof $
  [ Var <$> getPositive <$> arbitrary
  , CInt <$> arbitrary
  ] ++ if n == 0 then
    []
  else resize (n - 1) <$>
    [ If <$> genBool <*> genInt <*> genInt
    , Plus <$> genInt <*> genInt
    ]

genBool :: Gen Expr
genBool = sized $ \n -> oneof $
  [ CBool <$> arbitrary
  ] ++ if n == 0 then
    []
  else resize (n - 1) <$>
    [ If <$> genBool <*> genBool <*> genBool
    , Equal <$> genInt <*> genInt
    , And <$> genBool <*> genBool
    , Not <$> genBool
    ]

genExpr :: Type -> Gen Expr
genExpr t = sized $ \n -> oneof $
  [ If <$> genExpr TBool <*> genExpr t <*> genExpr t | n > 0 ] ++
  case t of
    TBool ->
      [ CBool <$> arbitrary
      ] ++ if n == 0 then
        []
      else resize (n - 1) <$>
        [ Equal <$> genExpr TInt <*> genExpr TInt
        , And <$> genExpr TBool <*> genExpr TBool
        , Not <$> genExpr TBool
        ]
    TInt ->
      [ Var <$> getPositive <$> arbitrary
      , CInt <$> arbitrary
      ] ++ if n == 0 then
        []
      else resize (n - 1) <$>
        [ Plus <$> genExpr TInt <*> genExpr TInt
        ]

type Pro p = (Properties p, Monad1 p, Alternative1 p)

gapExpr :: (?size :: Int, Pro p) => Type -> J p Expr
gapExpr t =
  let
    ?size = ?size - 1
  in
    withMonad $ do
      root <- Just =. finite roots
      case root of
        If{} -> do
          e0 <- cond =. gapExpr TBool
          e1 <- branch1 =. gapExpr t
          e2 <- branch2 =. gapExpr t
          return (If e0 e1 e2)
        Plus{} | TInt <- t -> do
          e1 <- operand1 =. gapExpr TInt
          e2 <- operand2 =. gapExpr TInt
          return (Plus e1 e2)
        Equal{} | TBool <- t -> do
          e1 <- operand1 =. gapExpr TInt
          e2 <- operand2 =. gapExpr TInt
          return (Equal e1 e2)
        And{} | TBool <- t -> do
          e1 <- operand1 =. gapExpr TBool
          e2 <- operand2 =. gapExpr TBool
          return (And e1 e2)
        Not{} | TBool <- t -> do
          e1 <- unNot =. gapExpr TBool
          return (Not e1)
        Var{} | TInt <- t -> do
          v <- unVar =. nonNegative 0.8
          return (Var v)
        CInt{} | TInt <- t -> do
          n <- unCInt =. integer 0.5
          return (CInt n)
        CBool{} | TBool <- t -> do
          b <- unCBool =. bernoulli 0.5
          return (CBool b)
        _ -> withAlternative empty
  where
    roots = case t of
      TInt | ?size == 0 -> [(1, CInt{}), (1, Var{})]
      TBool | ?size == 0 -> [(1, CBool{})]
      TInt -> [(1, If{}), (1, Plus{}), (1, CInt{}), (1, Var{})]
      TBool -> [(1, If{}), (1, CBool{}), (1, Equal{}), (1, Not{}), (1, And{})]

-- Type preserving shrink.
shrinkExpr e = shrinkExpr' e ++ recursivelyShrink e

shrinkExpr' e = case e of
  If _ e1 e2 -> [e1, e2]
  Plus e1 e2 -> [e1, e2]
  And e1 e2 -> [e1, e2]
  Not e -> [e]
  _ -> []

instance Arbitrary Expr where
  shrink = shrinkExpr

main = do
  let args = stdArgs{maxSize=1000, maxSuccess=1000}
  for_ [TInt, TBool] $ \t -> do
    quickCheckWith args $
      forAllShrink
        (logSize $ sized $ \n -> let ?size = n in runGenerator (gapExpr t))
        (\(Just e) -> Just <$> shrinkExpr e)
        $ \e ->
          case e of
            Nothing -> discard
            Just e -> typeOf e === pure t
    quickCheckWith args $
      forAllShrink
        (logSize $ genExpr t)
        shrinkExpr
        $ \e ->
          let ?size = -1 in applyPredicate (gapExpr t) e

logSize :: Gen a -> Gen a
logSize g = sized $ \n -> resize (round (log (fromIntegral (n+1)))) g
