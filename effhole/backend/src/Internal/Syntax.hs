{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}

module Internal.Syntax where

import Bound
import Common
import Control.Applicative
import Control.Monad
import Data.Eq.Deriving (deriveEq1)
import Data.Functor.Classes
import Text.Show.Deriving (deriveShow1)
import Type
import External (BindVar)

-- Now the internal term records the name of each variable
-- But the bound variables are still `Scope ()` instead of `Scope Id`
-- It is a balance of name recovery & easy alpha equivalence
data Expr a
  = Var a
  | BV Bool
  | NV Int
  | Str String
  | Unit
  | BiOp ArithOp (Expr a) (Expr a)
  | Nil
  | Cons (Expr a) (Expr a)
  | UnCons (Expr a) (Expr a) Id Id (Scope XOrK Expr a)
  | Abs Id (Scope () Expr a)
  | Pair (Expr a) (Expr a)
  | InLorR Bool (Expr a)
  | UnEither (Expr a) Id (Scope () Expr a) Id (Scope () Expr a)
  | Handler Id (Scope () Expr a) [(OpTag, (Id, Id, Scope XOrK Expr a))]
  | ExprHole Int (Maybe Int) [(BindVar, Expr a)]
  | App (Expr a) (Expr a)
  | If (Expr a) (Expr a) (Expr a)
  | Unpair (Expr a) Id Id (Scope XOrK Expr a)
  | OpCall Operation (Expr a)
  | With (Expr a) (Expr a)
  | Do (Expr a) Id (Scope () Expr a)
  | LetRec Id Id (Scope XOrK Expr a) (Scope () Expr a) -- letrec f x = e in e'
  deriving (Functor, Foldable, Traversable)

data XOrK = X | K deriving (Eq, Show)

data Operation = Operation OpTag | OpHole Int deriving (Eq, Show)

instance Applicative Expr where
  pure = Var
  (<*>) = ap

instance Monad Expr where
  return = pure
  Var x >>= f = f x
  BV b >>= _ = BV b
  NV n >>= _ = NV n
  Str s >>= _ = Str s
  Unit >>= _ = Unit
  BiOp op e1 e2 >>= f = BiOp op (e1 >>= f) (e2 >>= f)
  Nil >>= _ = Nil
  Cons e1 e2 >>= f = Cons (e1 >>= f) (e2 >>= f)
  UnCons e1 e2 x k scope >>= f = UnCons (e1 >>= f) (e2 >>= f) x k (scope >>>= f)
  Abs x e >>= f = Abs x (e >>>= f)
  Pair e1 e2 >>= f = Pair (e1 >>= f) (e2 >>= f)
  InLorR b e >>= f = InLorR b (e >>= f)
  UnEither e x le y re >>= f = UnEither (e >>= f) x (le >>>= f) y (re >>>= f)
  Handler x scope cases >>= f = Handler x (scope >>>= f) [(op, (x, k, case' >>>= f)) | (op, (x, k, case')) <- cases]
  ExprHole i j subst >>= f = ExprHole i j [(x, e >>= f) | (x, e) <- subst]
  App e1 e2 >>= f = App (e1 >>= f) (e2 >>= f)
  If e1 e2 e3 >>= f = If (e1 >>= f) (e2 >>= f) (e3 >>= f)
  Unpair e a b scope >>= f = Unpair (e >>= f) a b (scope >>>= f)
  OpCall op e >>= f = OpCall op (e >>= f)
  With e1 e2 >>= f = With (e1 >>= f) (e2 >>= f)
  Do e x scope >>= f = Do (e >>= f) x (scope >>>= f)
  LetRec f x scope e >>= g = LetRec f x (scope >>>= g) (e >>>= g)

abstract2 :: (Eq a) => a -> a -> Expr a -> Scope XOrK Expr a
abstract2 x k = abstract f
  where
    f y
      | y == x = Just X
      | y == k = Just K
      | otherwise = Nothing

instantiate2 :: Expr a -> Expr a -> Scope XOrK Expr a -> Expr a
instantiate2 x k = instantiate $ \case K -> k; X -> x

$(deriveShow1 ''Expr)

instance (Show a) => Show (Expr a) where
  showsPrec = liftShowsPrec showsPrec showList

$(deriveEq1 ''Expr)

instance (Eq a) => Eq (Expr a) where
  (==) = liftEq (==)
