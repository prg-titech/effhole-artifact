{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Internal.Pretty
  ( PrettyShow(..)
  , PrettyState(..)
  , precLambda
  , precIf
  , precCons
  , precEq
  , precConcat
  , precAdd
  , precMul
  , precApp
  , precAtom
  , arithPrec
  , needsParens
  , biOpPrecContexts
  , consPrecContexts
  , appPrecContexts
  , ifPrecContexts
  , withPrec
  , wrapIfNeeded
  , prettyArithOpDoc
  , prettyOperationDoc
  , renderBiOpDoc
  , renderConsDoc
  , renderCaseHeadDoc
  , renderCaseBlockDoc
  , renderUnConsDoc
  , renderPairDoc
  , renderInLorRDoc
  , renderUnEitherDoc
  , renderAppDoc
  , renderIfDoc
  , renderUnpairDoc
  , renderOpCallDoc
  , renderWithDoc
  , renderBindingDoc
  , renderDoDoc
  , renderLetRecDoc
  , prettyPrintPrec
  , prettyPrint
  , makeWidth
  , makeShow
  , prettyShow'
  , prettyShowWidth
  , prettyShow
  ) where

import Prettyprinter
import Internal.Syntax
import Common
import Control.Monad.Reader
import Type
import Bound
import Control.Monad
import Prettyprinter.Render.String (renderString)

-- class for pretty printing expressions
class (Pretty a, FreshName a, Show a) => PrettyShow a where
instance PrettyShow Id
data PrettyState = PrettyState
  { names :: Stream Id,
    prec :: Int, -- the precedence of the surrounding context, used for deciding when to add parentheses
    inDo :: Bool -- whether we are in the body of a do expression
  }

-- Precedence table (larger number binds tighter):
-- app > * / > + - > ^ > == > :: > if > lambda
precLambda, precIf, precCons, precEq, precConcat, precAdd, precMul, precApp, precAtom :: Int
precLambda = 0
precIf = 1
precCons = 2
precEq = 3
precConcat = 4
precAdd = 5
precMul = 6
precApp = 7
precAtom = 8

arithPrec :: ArithOp -> Int
arithPrec Add = precAdd
arithPrec Sub = precAdd
arithPrec Mul = precMul
arithPrec Div = precMul
arithPrec Eqi = precEq
arithPrec Neq = precEq
arithPrec Lt = precEq
arithPrec Le = precEq
arithPrec Gt = precEq
arithPrec Ge = precEq
arithPrec Concat = precConcat

needsParens :: Int -> Int -> Bool
needsParens selfPrec ctxPrec = selfPrec < ctxPrec

biOpPrecContexts :: ArithOp -> (Int, Int, Int)
biOpPrecContexts op =
  let p = arithPrec op
   in case op of
        Eqi -> (p, p + 1, p + 1)
        Neq -> (p, p + 1, p + 1)
        Lt -> (p, p + 1, p + 1)
        Le -> (p, p + 1, p + 1)
        Gt -> (p, p + 1, p + 1)
        Ge -> (p, p + 1, p + 1)
        _ -> (p, p, p + 1)

consPrecContexts :: (Int, Int, Int)
consPrecContexts = (precCons, precCons + 1, precCons)

appPrecContexts :: (Int, Int, Int)
appPrecContexts = (precApp, precApp, precLambda)

ifPrecContexts :: (Int, Int)
ifPrecContexts = (precIf, precIf)

withPrec :: MonadReader PrettyState m => Int -> m a -> m a
withPrec p = local (\s -> s {prec = p})

wrapIfNeeded :: MonadReader PrettyState m => Int -> Doc ann -> m (Doc ann)
wrapIfNeeded p doc = do
  ctx <- asks prec
  return $ if needsParens p ctx then parens doc else doc

prettyArithOpDoc :: ArithOp -> Doc ann
prettyArithOpDoc Add = "+"
prettyArithOpDoc Sub = "-"
prettyArithOpDoc Mul = "*"
prettyArithOpDoc Div = "/"
prettyArithOpDoc Eqi = "=="
prettyArithOpDoc Neq = "/="
prettyArithOpDoc Lt = "<"
prettyArithOpDoc Le = "<="
prettyArithOpDoc Gt = ">"
prettyArithOpDoc Ge = ">="
prettyArithOpDoc Concat = "^"

prettyOperationDoc :: Operation -> Doc ann
prettyOperationDoc (Operation op) = pretty op
prettyOperationDoc (OpHole i) = pretty ("?" ++ show i)

renderBiOpDoc :: ArithOp -> Doc ann -> Doc ann -> Doc ann
renderBiOpDoc op e1 e2 = group (e1 <> line <> prettyArithOpDoc op <+> e2)

renderConsDoc :: Doc ann -> Doc ann -> Doc ann
renderConsDoc e1 e2 = group (e1 <> line <> "::" <+> e2)

renderCaseHeadDoc :: Doc ann -> Doc ann
renderCaseHeadDoc scrutinee = group (scrutinee <+> "match" <+> lbrace)

renderCaseBlockDoc :: Doc ann -> [Doc ann] -> Doc ann
renderCaseBlockDoc scrutinee branches =
  let branchesDoc = vsep (punctuate semi branches)
      multiLine =
        vsep
          [ renderCaseHeadDoc scrutinee,
            indent 2 (align branchesDoc),
            rbrace
          ]
      singleLine = renderCaseHeadDoc scrutinee <+> hsep (punctuate semi branches) <+> rbrace
   in group (flatAlt multiLine singleLine)

renderUnConsDoc :: Id -> Id -> Doc ann -> Doc ann -> Doc ann -> Doc ann
renderUnConsDoc x k scrutinee nilDoc consDoc =
  renderCaseBlockDoc
    scrutinee
    [ "[] =>" <+> nilDoc,
      pretty x <+> "::" <+> pretty k <+> "=>" <+> consDoc
    ]

renderPairDoc :: Doc ann -> Doc ann -> Doc ann
renderPairDoc e1 e2 = parens (e1 <> ", " <> e2)

renderInLorRDoc :: Bool -> Doc ann -> Doc ann
renderInLorRDoc b e = (if b then "inl" else "inr") <+> e

renderUnEitherDoc :: Id -> Id -> Doc ann -> Doc ann -> Doc ann -> Doc ann
renderUnEitherDoc x y scrutinee leftDoc rightDoc =
  renderCaseBlockDoc
    scrutinee
    [ "inl" <+> pretty x <+> "=>" <+> leftDoc,
      "inr" <+> pretty y <+> "=>" <+> rightDoc
    ]

renderAppDoc :: Doc ann -> Doc ann -> Doc ann
renderAppDoc e1 e2 = e1 <> parens e2

renderIfDoc :: Doc ann -> Doc ann -> Doc ann -> Doc ann
renderIfDoc condDoc thenDoc elseDoc =
  let multiLine = vsep
          [ "if" <+> condDoc,
            indent 2 . align $ vsep ["then" <+> thenDoc, "else" <+> elseDoc]
          ]
      singleLine = "if" <+> condDoc <+> "then" <+> thenDoc <+> "else" <+> elseDoc
   in group (flatAlt multiLine singleLine)

renderUnpairDoc :: Id -> Id -> Doc ann -> Doc ann -> Doc ann
renderUnpairDoc a b scrutinee bodyDoc =
  let branchDoc = parens (pretty a <> ", " <> pretty b) <+> "=>" <+> bodyDoc
   in renderCaseBlockDoc scrutinee [branchDoc]

renderOpCallDoc :: Operation -> Doc ann -> Doc ann
renderOpCallDoc op e = "#" <> prettyOperationDoc op <> parens e

renderWithDoc :: Doc ann -> Doc ann -> Doc ann
renderWithDoc h body = align $ vsep ["with" <+> h, "handle" <+> lbrace, indent 2 body, rbrace]

renderBindingDoc :: Id -> Doc ann -> Doc ann
renderBindingDoc x rhs
  | x == dummy = rhs
  | otherwise = "val" <+> pretty x <+> "=" <+> rhs

renderDoDoc :: Bool -> Id -> Doc ann -> Doc ann -> Doc ann
renderDoDoc isNested x rhs body =
  let stmt = renderBindingDoc x rhs <> semi
   in
    if isNested
      then vsep [stmt, body]
      else
        let multiLine =
              vsep
                [ lbrace,
                  indent 2 . align $ vsep [stmt, body],
                  rbrace
                ]
            singleLine = lbrace <+> stmt <+> body <+> rbrace
         in group (flatAlt multiLine singleLine)

renderLetRecDoc :: Bool -> Id -> Id -> Doc ann -> Doc ann -> Doc ann
renderLetRecDoc isNested f x rhs body =
  let stmt = "def" <+> pretty f <+> parens (pretty x) <+> "=" <+> rhs <> semi
   in
    if isNested
      then vsep [stmt, body]
      else
        let multiLine =
              vsep
                [ lbrace,
                  indent 2 . align $ vsep [stmt, body],
                  rbrace
                ]
            singleLine = lbrace <+> stmt <+> body <+> rbrace
         in group (flatAlt multiLine singleLine)

-- TODO: the first argument Stream is not used
-- HACK: replace the dummy name with a good name in the stream
prettyPrintPrec :: MonadReader PrettyState m => Expr Id -> m (Doc ann)
prettyPrintPrec (Var x) = return $ pretty x
prettyPrintPrec (BV b) = return $ pretty (show b)
prettyPrintPrec (NV n) = return $ pretty (show n)
prettyPrintPrec (Str s) = return $ pretty (show s)
prettyPrintPrec Unit = return "()"
prettyPrintPrec (BiOp op e1 e2) = do
  let (p, leftCtx, rightCtx) = biOpPrecContexts op
  e1' <- withPrec leftCtx (prettyPrintPrec e1)
  e2' <- withPrec rightCtx (prettyPrintPrec e2)
  wrapIfNeeded p (renderBiOpDoc op e1' e2')
prettyPrintPrec Nil = return "[]"
prettyPrintPrec (Cons e1 e2) = do
  let (p, leftCtx, rightCtx) = consPrecContexts
  e1' <- withPrec leftCtx (prettyPrintPrec e1)
  e2' <- withPrec rightCtx (prettyPrintPrec e2)
  wrapIfNeeded p (renderConsDoc e1' e2')
prettyPrintPrec (UnCons e1 e2 x k scope) = do
  let consExpr = instantiate2 (Var x) (Var k) scope
  e1' <- prettyPrintPrec e1
  nilDoc <- prettyPrintPrec e2
  consDoc <- prettyPrintPrec consExpr
  return $ renderUnConsDoc x k e1' nilDoc consDoc
prettyPrintPrec (Abs x scope) = do
  let e = instantiate1 (Var x) scope
  e' <- withPrec precLambda (prettyPrintPrec e)
  let doc = group ("\\" <> pretty x <> "." <> nest 2 (line <> e'))
  wrapIfNeeded precLambda doc
prettyPrintPrec (Pair e1 e2) = do
  e1' <- prettyPrintPrec e1
  e2' <- prettyPrintPrec e2
  return $ renderPairDoc e1' e2'
prettyPrintPrec (InLorR b e) = do
  e' <- prettyPrintPrec e
  return $ renderInLorRDoc b e'
prettyPrintPrec (UnEither e x le y re) = do
  let le' = instantiate1 (Var x) le
  let re' = instantiate1 (Var y) re
  e' <- prettyPrintPrec e
  le'' <- prettyPrintPrec le'
  re'' <- prettyPrintPrec re'
  return $ renderUnEitherDoc x y e' le'' re''
prettyPrintPrec (Handler x scope cases) = do
  let e = instantiate1 (Var x) scope
  pcases' <- vsep . punctuate semi <$> pcases
  e' <- prettyPrintPrec e
  let doc = vsep [ "handler" <+> lbrace
                 , indent 2 . align $ pretty x <+> "=>" <+> e' <+> semi
                 , indent 2 . align $ pcases'
                 , rbrace]
  return $ doc
  where
    pcases = forM cases $ \(op, (caseX, caseK, caseScope)) -> do
      let case' = instantiate2 (Var caseX) (Var caseK) caseScope
      case'Doc <- prettyPrintPrec case'
      let headDoc = pretty op <> parens (pretty caseX <> ", " <> pretty caseK) <+> "=>"
      return $ group (headDoc <> line <> nest 2 (align case'Doc))
prettyPrintPrec (ExprHole i Nothing _) = return $ pretty ("?" ++ show i ++ "__")  -- HACK
prettyPrintPrec (ExprHole i (Just j) _) = return $ pretty ("?" ++ show i ++ "_" ++ show j)
prettyPrintPrec (App e1 e2) = do
  let (p, leftCtx, rightCtx) = appPrecContexts
  e1' <- withPrec leftCtx (prettyPrintPrec e1)
  e2' <- withPrec rightCtx (prettyPrintPrec e2)
  wrapIfNeeded p (renderAppDoc e1' e2')
prettyPrintPrec (If e1 e2 e3) = do
  let (p, childCtx) = ifPrecContexts
  e1' <- withPrec childCtx (prettyPrintPrec e1)
  e2' <- withPrec childCtx (prettyPrintPrec e2)
  e3' <- withPrec childCtx (prettyPrintPrec e3)
  wrapIfNeeded p (renderIfDoc e1' e2' e3')
prettyPrintPrec (Unpair e a b scope) = do
  let e2 = instantiate2 (Var a) (Var b) scope
  e' <- prettyPrintPrec e
  e2' <- prettyPrintPrec e2
  return $ renderUnpairDoc a b e' e2'
prettyPrintPrec (OpCall op e) = do
  e' <- prettyPrintPrec e
  return $ renderOpCallDoc op e'
prettyPrintPrec (With e1 e2) = do
  e1' <- prettyPrintPrec e1
  e2' <- prettyPrintPrec e2
  return $ renderWithDoc e1' e2'
prettyPrintPrec (Do e x scope) = do
  inDoFlag <- asks inDo
  -- rhs of a binding is not special, print normally
  e' <- local (\st -> st {inDo = False}) (prettyPrintPrec e)
  bodyDoc <- printIfDo (instantiate1 (Var x) scope)
  return $ renderDoDoc inDoFlag x e' bodyDoc
  where
    -- if the nested expression is also a do, then we only print the binding part
    -- otherwise we set inDo to False, and print the expression normally
    printIfDo expr@Do{} = local (\st -> st {inDo = True}) (prettyPrintPrec expr)
    printIfDo expr@LetRec{} = local (\st -> st {inDo = True}) (prettyPrintPrec expr)
    printIfDo expr = local (\st -> st {inDo = False}) (prettyPrintPrec expr)

prettyPrintPrec (LetRec f x s1 s2) = do
  inDoFlag <- asks inDo
  let rhsExpr = instantiate2 (Var f) (Var x) s1
  rhsDoc <- local (\st -> st {inDo = False}) (prettyPrintPrec rhsExpr)
  bodyDoc <- printIfDo (instantiate1 (Var f) s2)
  return $ renderLetRecDoc inDoFlag f x rhsDoc bodyDoc
  where
    printIfDo expr@Do{} = local (\st -> st {inDo = True}) (prettyPrintPrec expr)
    printIfDo expr@LetRec{} = local (\st -> st {inDo = True}) (prettyPrintPrec expr)
    printIfDo expr = local (\st -> st {inDo = False}) (prettyPrintPrec expr)

prettyPrint :: Expr Id -> Doc ann
prettyPrint e = let s = PrettyState {names = freshnames, inDo = False, prec = 0}
                 in runReader (prettyPrintPrec e) s

makeWidth :: (LayoutOptions -> a) -> Int -> a
makeWidth f x = f (LayoutOptions (AvailablePerLine x 1.0))

makeShow :: (LayoutOptions -> a) -> a
makeShow f = f defaultLayoutOptions

prettyShow' :: LayoutOptions -> Expr Id -> String
prettyShow' layout = renderString . layoutPretty layout . prettyPrint 

prettyShowWidth :: Int -> Expr Id -> String
prettyShowWidth = makeWidth prettyShow'

prettyShow :: Expr Id -> String
prettyShow = makeShow prettyShow'
