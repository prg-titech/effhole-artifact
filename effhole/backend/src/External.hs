{-# LANGUAGE OverloadedStrings #-}

module External where

import Prettyprinter
import Common
import Type

-- record the name and position of each variable of a binder
data BindVar = BindVar 
  { name     :: Id
  , startPos :: CodePos
  , endPos   :: CodePos
  } deriving (Show, Eq)

data Expr
  = Var Id
  | BV Bool
  | NV Int
  | Str String
  | Unit
  | BiOp ArithOp Expr Expr
  | Nil
  | Cons Expr Expr
  | UnCons Expr Expr BindVar BindVar Expr
  | Abs BindVar [BindVar] Expr
  | Pair Expr Expr
  | InLorR Bool Expr -- True for left, False for right
  | UnEither Expr BindVar Expr BindVar Expr
  | Handler BindVar Expr [HandlerCase]
  | ExprHole Int
  | App Expr Expr
  | If Expr Expr Expr
  | Unpair Expr BindVar BindVar Expr
  | OpCall Operation Expr
  | With Expr Expr
  | Do [DoStmt] Expr deriving (Show, Eq)

data DoStmt = DoBind BindVar Expr | DoExpr Expr | LetRec BindVar BindVar [BindVar] Expr deriving (Show, Eq)
data HandlerCase = HandlerCase OpTag BindVar BindVar Expr deriving (Show, Eq)

data Operation = Operation OpTag | OpHole Int deriving (Show, Eq)
