{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
module Type where

import Data.String
import qualified Data.Set as S
import Common
import qualified Data.Text as T
import Prettyprinter

data ArithOp = Add | Sub | Mul | Div | Eqi | Neq | Lt | Le | Gt | Ge | Concat deriving (Eq, Show)

infixl 8 :->
infixl 8 :=>
  
data ValueType
  = TVoid | TUnit | TBool | TInt
  | ValueType :-> CompType
  | ValueHoleType
  | CompType :=> CompType
  deriving (Eq)

infix 9 :!
data CompType = ValueType :! Dirt
  deriving (Eq)

newtype OpTag = OpTag Id deriving (Eq, Ord)
data OperationType
  = Op OpTag
  | OpHoleType Int
  deriving (Eq, Ord)
  
data Dirt
  = Dirt (S.Set OperationType)
  | DirtWithCompHole (S.Set OperationType)
  deriving (Eq)

dirt0 :: Dirt
dirt0 = DirtWithCompHole S.empty
comphole0 :: CompType
comphole0 = ValueHoleType :! dirt0 

split :: S.Set OperationType -> (S.Set OperationType, S.Set OperationType)
split = S.partition $ \case { Op{} -> True; OpHoleType _ -> False }

-- the union of two dirts
union :: Dirt -> Dirt -> Dirt
union (Dirt d1) (Dirt d2) = Dirt $ S.union d1 d2
union (DirtWithCompHole d1) (Dirt d2) = DirtWithCompHole $ S.union d1 d2
union (Dirt d1) (DirtWithCompHole d2) = DirtWithCompHole $ S.union d1 d2
union (DirtWithCompHole d1) (DirtWithCompHole d2) = DirtWithCompHole $ S.union d1 d2

isElem :: OperationType -> Dirt -> Bool
isElem op (Dirt d) = S.member op d
isElem _ DirtWithCompHole{} = True

-- if d1 is a subset of d2
-- TODO: check this
isSubsetOf :: Dirt -> Dirt -> Bool
isSubsetOf (Dirt d1) (Dirt d2) = S.isSubsetOf d1 d2
isSubsetOf (DirtWithCompHole d1) (Dirt d2) = False
isSubsetOf _ (DirtWithCompHole _) = True

instance Pretty ValueType where
  pretty TVoid = "Void"
  pretty TUnit = "()"
  pretty TBool = "Bool"
  pretty TInt = "Int"
  pretty ValueHoleType = "?"
  pretty (v :-> c) = -- pretty v <+> "->" <+> pretty c
    parens (pretty v) <+> "->" <+> parens (pretty c)
  pretty (c1 :=> c2) = pretty c1 <+> "|=>" <+> pretty c2

instance Pretty CompType where
  pretty (v :! d) = pretty v <> "/" <> pretty d

instance Pretty OpTag where
  pretty (OpTag op) = pretty op  

instance Pretty OperationType where
  pretty (Op op) = pretty op
  pretty (OpHoleType i) = "#?" <> pretty i

instance Pretty Dirt where
  pretty (Dirt d) = braces . hsep $ punctuate comma (pretty <$> S.toList d)
  pretty (DirtWithCompHole d) 
    | S.null d = "{?}"
    | otherwise = braces (hsep $ punctuate comma (pretty <$> S.toList d)) <+> "U" <+> "{?}"

instance Show ValueType where
  show = show . pretty
instance Show CompType where
  show = show . pretty
instance Show OpTag where
  show = show . pretty
instance Show OperationType where
  show = show . pretty
instance Show Dirt where
  show = show . pretty

-- smart constructors
(?!) :: ValueType -> [OperationType] -> CompType
v ?! ops = v :! Dirt (S.fromList ops)


instance IsString OpTag where
  fromString = OpTag . T.pack
instance IsString OperationType where
  fromString = Op . OpTag . T.pack
  
-- t1 = ValueHoleType ?! ["print", "read", OpHoleType 1]
-- t2 = (TUnit :-> t1) ?! []
-- t3 = t1 :=> t2
