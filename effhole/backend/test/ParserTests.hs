{-# LANGUAGE OverloadedStrings #-}
module ParserTests where

import Control.Applicative hiding (some)
import Data.Either (isLeft)
import Data.List (isInfixOf)
import qualified Data.Text as T
import Data.Void
import Test.Hspec
import Test.Hspec.Megaparsec
import Text.Megaparsec
import Text.Megaparsec.Char
import Parser
import External (Expr(..), DoStmt(..), HandlerCase(..), Operation(..), BindVar(..))
import Type
import Common

infixr 0 !

(!) :: Id -> Expr -> Expr 
x ! e = Abs (bv x) [] e 

v :: Id -> Expr 
v = Var

infixl 9 @
(@) :: Expr -> Expr -> Expr 
(@) = App

dummyPos = (0, 0)

bv x = BindVar x dummyPos dummyPos

stripPos :: Expr -> Expr
stripPos = go
  where
    go (Var x) = Var x
    go (BV b) = BV b
    go (NV n) = NV n
    go (Str s) = Str s
    go Unit = Unit
    go (BiOp op e1 e2) = BiOp op (go e1) (go e2)
    go Nil = Nil
    go (Cons e1 e2) = Cons (go e1) (go e2)
    go (UnCons e1 e2 x k e) = UnCons (go e1) (go e2) (bv $ name x) (bv $ name k) (go e)
    go (Abs x xs e) = Abs (bv $ name x) (map (bv . name) xs) (go e)
    go (Pair e1 e2) = Pair (go e1) (go e2)
    go (InLorR b e) = InLorR b (go e)
    go (UnEither e x le y re) = UnEither (go e) (bv $ name x) (go le) (bv $ name y) (go re)
    go (Handler x e cases) = Handler (bv $ name x) (go e) [ HandlerCase op (bv $ name a) (bv $ name k) (go case') | HandlerCase op a k case' <- cases ]
    go (ExprHole i) = ExprHole i
    go (App e1 e2) = App (go e1) (go e2)
    go (If e1 e2 e3) = If (go e1) (go e2) (go e3)
    go (Unpair e a b e') = Unpair (go e) (bv $ name a) (bv $ name b) (go e')
    go (OpCall op e) = OpCall op (go e)
    go (With e1 e2) = With (go e1) (go e2)
    go (Do stmts e) = Do (map goStmt stmts) (go e)
    goStmt (DoBind x e) = DoBind (bv $ name x) (go e)
    goStmt (DoExpr e) = DoExpr (go e)
    goStmt (LetRec f x xs e) = LetRec (bv $ name f) (bv $ name x) (map (bv . name) xs) (go e)

testParser = [ testSimple, testParseVar, testParseAbs, testParsePair
             , testParseHandler, testParseOpCall, testParseDo, testParseBiOp, testParseUnCons
             , testParseUnEither, testParseErrors ]

testSimple =
  describe "simple parsers" $ do
    it "parses a simple expression" $ do
      runStateParser' parseBool "True" `shouldParse` BV True
      runStateParser' parseBool "False" `shouldParse` BV False
      runStateParser' parseUnit "()" `shouldParse` Unit
      runStateParser' parseHole "?1" `shouldParse` ExprHole 1

testParseVar =
  describe "parseVar" $ do
    it "parses an identifier" $ do
      runStateParser' parseVar "a123" `shouldParse` Var "a123"

testParseAbs = 
  describe "parseAbs" $ do
    it "parses a lambda expression" $ do
      runStateParser' (fmap stripPos parseExpr) "\\x. x" `shouldParse` ("x" ! Var "x")
      runStateParser' (fmap stripPos parseExpr) "\\x y z. x" `shouldParse` Abs (bv "x") [bv "y", bv "z"] (Var "x")
      runStateParser' (fmap stripPos parseExpr) "\\x. x(x)" `shouldParse` ("x" ! App (Var "x") (Var "x"))
      runStateParser' (fmap stripPos parseExpr) "\\x. \\y. y(x)(x)" `shouldParse` 
        Abs (bv "x") [bv "y"] (App (App (Var "y") (Var "x")) (Var "x"))
      runStateParser' (fmap stripPos parseExpr) "(\\f. (\\x . f(\\v.v)(\\y. f(1))))(2)" `shouldParse` 
        App (Abs (bv "f") [bv "x"] (App (Var "f") (Abs (bv "v") [] (Var "v")) `App` Abs (bv "y") [] (App (Var "f") (NV 1)))) (NV 2)
      runStateParser' (fmap stripPos parseExpr) (T.pack $ "(\\f. \\x. f(\\v. x(x)(v))(\\x. f(\\v. x(x)(v))))" ++
                  "(\\fact. \\n. if n == 0 then 1 else n * fact(n - 1))(1)")
        `shouldParse` (fix @ fact @ NV 1)
      runStateParser' parseExpr "f x" `shouldSatisfy` isLeft
  where
      fix = Abs (bv "f") [bv "x"]
              (App
                (App (v "f") (Abs (bv "v") [] (App (App (v "x") (v "x")) (v "v"))))
                (Abs (bv "x") [] (App (v "f") (Abs (bv "v") [] (App (App (v "x") (v "x")) (v "v")))))
              )
      fact = Abs (bv "fact") [bv "n"] (If (BiOp Eqi (v "n") (NV 0)) (NV 1) (BiOp Mul (v"n") (v "fact" @ BiOp Sub (v"n") (NV 1))))

testParsePair =
  describe "parsePair" $ do
    it "parses a pair expression" $ do
      runStateParser' parseExpr "(True, 42)" `shouldParse` Pair (BV True) (NV 42)
  
testParseHandler =
  describe "parseHandler" $ do
    it "parses a handler expression" $ do
      runStateParser' (fmap stripPos parseExpr) "handler { x => x; get(x, k) => \\s. s; put(v, k) => \\s. s}" `shouldParse`
        Handler (bv "x") (Var "x") [ HandlerCase "get" (bv "x") (bv "k") (Abs (bv "s") [] (Var "s")),
                              HandlerCase "put" (bv "v") (bv "k") (Abs (bv "s") [] (Var "s"))]

testParseOpCall =
  describe "parseOpCall" $ do
    it "parses an explicit operation call" $ do
      runStateParser' parseExpr "#get(1)" `shouldParse`
        OpCall (Operation "get") (NV 1)

testParseDo =
  describe "parseDo" $ do
    it "parses a do expression with letrec" $ do
       runStateParser' (fmap stripPos parseDo) "{ def f(x) = x; f(1) }" `shouldParse`
         Do [LetRec (bv "f") (bv "x") [] (Var "x")] (App (Var "f") (NV 1))

    it "parses a do expression with multi-parameter letrec" $ do
       runStateParser' (fmap stripPos parseDo) "{ def f(x)(y) = x; f(1)(2) }" `shouldParse`
         Do [LetRec (bv "f") (bv "x") [bv "y"] (Var "x")] (App (App (Var "f") (NV 1)) (NV 2))

    it "parses a do expression with mixed statements" $ do
      runStateParser' (fmap stripPos parseDo) "{ def f(y) = y; 42 }" `shouldParse`
        Do [ LetRec (bv "f") (bv "y") [] (Var "y") ] (NV 42)

    it "parses a do expression with only return expr" $ do
      runStateParser' (fmap stripPos parseDo) "{ 42 }" `shouldParse`
        Do [] (NV 42)

    it "keeps syntax errors inside val rhs" $ do
      case runStateParser' (fmap stripPos parseDo) "{ val pickAll = handler { x => [x] decide(x, k) => ? (k(True)) (k(False)) }; with pickAll handle { choose(15)(30) - choose(5)(10) } }" of
        Left parseErr -> errorBundlePretty parseErr `shouldSatisfy` not . isInfixOf "reserved word \"val\" cannot be an identifier"
        Right _ -> expectationFailure "expected parse failure"

testParseBiOp =
  describe "parseBiOp" $ do
    it "parses binary operations with correct precedence" $ do
      runStateParser' parseExpr "1 + 2" `shouldParse` BiOp Add (NV 1) (NV 2)
      runStateParser' parseExpr "1 + 2 * 3" `shouldParse` BiOp Add (NV 1) (BiOp Mul (NV 2) (NV 3))
      runStateParser' parseExpr "(1 + 2) * 3" `shouldParse` BiOp Mul (BiOp Add (NV 1) (NV 2)) (NV 3)
      runStateParser' parseExpr "1 :: 2 :: []" `shouldParse` Cons (NV 1) (Cons (NV 2) Nil)
      runStateParser' parseExpr "1 + 1 :: 2 :: []" `shouldParse` Cons (BiOp Add (NV 1) (NV 1)) (Cons (NV 2) Nil)
      runStateParser' parseExpr "\"a\" ^ \"b\"" `shouldParse` BiOp Concat (Str "a") (Str "b")
      runStateParser' parseExpr "1 < 2" `shouldParse` BiOp Lt (NV 1) (NV 2)
      runStateParser' parseExpr "1 <= 2" `shouldParse` BiOp Le (NV 1) (NV 2)
      runStateParser' parseExpr "2 > 1" `shouldParse` BiOp Gt (NV 2) (NV 1)
      runStateParser' parseExpr "2 >= 1" `shouldParse` BiOp Ge (NV 2) (NV 1)
      runStateParser' parseExpr "1 /= 2" `shouldParse` BiOp Neq (NV 1) (NV 2)
      -- negative number literals
      runStateParser' parseExpr "-42" `shouldParse` NV (-42)
      runStateParser' parseExpr "-1 + 2" `shouldParse` BiOp Add (NV (-1)) (NV 2)
      runStateParser' parseExpr "1 + -2" `shouldParse` BiOp Add (NV 1) (NV (-2))

testParseUnCons =
  describe "parseUnCons" $ do
    it "parses an uncons expression" $ do
      runStateParser' (fmap stripPos parseExpr) "xs match { [] => 0; x :: xs => x }" `shouldParse`
        UnCons (Var "xs") (NV 0) (bv "x") (bv "xs") (Var "x")

    it "parses an uncons expression with cons case first" $ do
      runStateParser' (fmap stripPos parseExpr) "xs match { x :: xs => x; [] => 0 }" `shouldParse`
        UnCons (Var "xs") (NV 0) (bv "x") (bv "xs") (Var "x")

testParseUnEither =
  describe "parseUnEither" $ do
    it "parses an uneither expression" $ do
      runStateParser' (fmap stripPos parseExpr) "e match { inl x => e1; inr y => e2 }" `shouldParse`
        UnEither (Var "e") (bv "x") (Var "e1") (bv "y") (Var "e2")
      runStateParser' (fmap stripPos parseExpr) "(inl 1) match { inl x => x; inr y => y }" `shouldParse`
        UnEither (InLorR True (NV 1)) (bv "x") (Var "x") (bv "y") (Var "y")

testParseErrors =
  describe "parse errors" $ do
    it "reports human readable labels for invalid atoms" $ do
      case runStateParser' parseExpr "@" of
        Left parseErr -> do
          let rendered = errorBundlePretty parseErr
          rendered `shouldSatisfy` ("integer literal" `isInfixOf`)
          rendered `shouldSatisfy` ("operation call" `isInfixOf`)
        Right _ -> expectationFailure "expected parse failure"

    it "reports a missing closing paren at the application site" $ do
      case runStateParser' parseExpr "f(1" of
        Left parseErr -> do
          let rendered = errorBundlePretty parseErr
          rendered `shouldSatisfy` ("1:4:" `isInfixOf`)
          rendered `shouldSatisfy` ("application argument" `isInfixOf`)
        Right _ -> expectationFailure "expected parse failure"

    it "reports a missing lambda dot at the dot site" $ do
      case runStateParser' parseExpr "\\ s  (x, s)" of
        Left parseErr -> errorBundlePretty parseErr `shouldSatisfy` ("'.' after lambda parameters" `isInfixOf`)
        Right _ -> expectationFailure "expected parse failure"

    it "reports prefix match syntax as postfix syntax" $ do
      case runStateParser' parseExpr "match \\x. (inr 1) { inl x => x + 1 ; inr x => x + 2 }" of
        Left parseErr -> errorBundlePretty parseErr `shouldSatisfy` ("match is a postfix form" `isInfixOf`)
        Right _ -> expectationFailure "expected parse failure"
