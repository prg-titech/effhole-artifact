{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
module Common where

import Control.Monad
import qualified Data.Text as T
import Prettyprinter
import Control.Monad.Except

type Id = T.Text

infixr 5 :<
data Stream a = a :< (Stream a) deriving (Show, Eq, Functor)

listToStream :: [a] -> Stream a
listToStream = foldr (:<) (error "Cannot convert empty list to stream")

filterStream :: (a -> Bool) -> Stream a -> Stream a
filterStream p (x :< xs)
  | p x       = x :< filterStream p xs
  | otherwise = filterStream p xs

class FreshName a where
  freshnames :: Stream a

instance FreshName T.Text where
  freshnames = listToStream freshnames'
    where
      freshnames' = map T.pack $ [1..] >>= flip replicateM ['a'..'z']

parensIf :: Bool -> Doc ann -> Doc ann
parensIf True = parens
parensIf False = id

-- TODO:
-- HACK: This is a name for internal usage only 
dummy :: Id
dummy = "$"

dummy' :: Id -> Id
dummy' = (<>) dummy

internalError :: (MonadError String m) => String -> m a
internalError err = throwError $ "Internal Error: Sorry, please report this as a bug!\n" ++ err

-- (line, column)
type CodePos = (Int, Int)
