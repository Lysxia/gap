{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}

module Expr where

import Control.Applicative
import Test.QuickCheck
import Generator.Predicate
import Profunctor.Monad

data Expr
  = If Expr Expr Expr
  | Plus Expr Expr
  | CInt Int
  | CBool Bool
  | Equal Expr Expr
  | Not Expr
  | And Expr Expr
  | Var Var
  deriving Show

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
  CInt _ -> return TInt
  CBool _ -> return TBool
  Equal e1 e2 -> do
    [t1, t2] <- traverse typeOf [e1, e2]
    assert (t1 == TInt && t2 == TInt) "Compare Int"
    return TBool
  Not e1 -> do
    t1 <- typeOf e1
    assert (t1 == TBool) "Not Bool"
    return TBool
  And e1 e2 -> do
    [t1, t2] <- traverse typeOf [e1, e2]
    assert (t1 == TBool && t2 == TBool) "And bool"
    return TBool
  Var _ -> return TInt

genInt :: Gen Expr
genInt = oneof
  [ If <$> genBool <*> genInt <*> genInt
  , Plus <$> genInt <*> genInt
  , CInt <$> arbitrary
  , Var <$> arbitrary
  ]

genBool :: Gen Expr
genBool = oneof
  [ If <$> genBool <*> genBool <*> genBool
  , CBool <$> arbitrary
  , Equal <$> genInt <*> genInt
  , Not <$> genBool
  , And <$> genBool <*> genBool
  ]

genExpr :: Type -> Gen Expr
genExpr t = oneof $
  [ If <$> genExpr TBool <*> genExpr t <*> genExpr t ] ++
  case t of
    TBool ->
      [ CBool <$> arbitrary
      , Equal <$> genExpr TInt <*> genExpr TInt
      , Not <$> genExpr TBool
      , And <$> genExpr TBool <*> genExpr TBool
      ]
    TInt ->
      [ Plus <$> genExpr TInt <*> genExpr TInt
      , CInt <$> arbitrary
      , Var <$> arbitrary
      ]

type Pro p = (Properties p, Monad1 p, Alternative1 p)

gapExpr :: Pro p => Type -> J p Expr
gapExpr t = with' @Monad $ do
  root <- Just =. finite roots
  case root of
    If{} -> do
      e0 <- cond =. gapExpr TBool
      e1 <- branch1 =. gapExpr t
      e2 <- branch2 =. gapExpr t
      return (If e0 e1 e2)
      where
        cond (If e0 _ _) = e0
        branch1 (If _ e1 _) = e1
        branch2 (If _ _ e2) = e2
    Plus{} | TInt <- t -> do
      e1 <- operand1 =. gapExpr TInt
      e2 <- operand2 =. gapExpr TInt
      return (Plus e1 e2)
      where
        operand1 (Plus e1 _) = e1
        operand2 (Plus _ e2) = e2
    CInt{} | TInt <- t -> do
      n <- unCInt =. nonNegative 0.5
      return (CInt n)
      where
        unCInt (CInt n) = n
    Var{} | TInt <- t -> do
      v <- unVar =. nonNegative 0.8
      return (Var v)
      where
        unVar (Var v) = v
    CBool{} | TBool <- t -> do
      b <- unCBool =. bernoulli 0.5
      return (CBool b)
      where
        unCBool (CBool b) = b
    Equal{} | TBool <- t -> do
      e1 <- operand1 =. gapExpr TInt
      e2 <- operand2 =. gapExpr TInt
      return (Equal e1 e2)
      where
        operand1 (Equal e1 _) = e1
        operand2 (Equal _ e2) = e2
    Not{} | TBool <- t -> do
      e1 <- unNot =. gapExpr TBool
      return (Not e1)
      where
        unNot (Not e1) = e1
    And{} | TBool <- t -> do
      e1 <- operand1 =. gapExpr TBool
      e2 <- operand2 =. gapExpr TBool
      return (And e1 e2)
      where
        operand1 (And e1 _) = e1
        operand2 (And _ e2) = e2
  where
    roots = case t of
      TInt -> [(1, If{}), (1, Plus{}), (1, CInt{}), (1, Var{})]
      TBool -> [(1, If{}), (1, CBool{}), (1, Equal{}), (1, Not{}), (1, And{})]
