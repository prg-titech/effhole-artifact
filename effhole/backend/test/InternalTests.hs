{-# LANGUAGE OverloadedStrings #-}

module InternalTests where

import Internal
import Type
import Common
import qualified External as E
import Prelude hiding (const)
import Test.Hspec
import Bound
import System.Timeout (timeout)
import Data.Maybe (isJust)

-- useful notations
infixr 0 !

(!) :: Id -> Expr Id -> Expr Id
x ! val = Abs x $ abstract1 x val 

v :: Id -> Expr Id
v = Var

vt, vf :: Expr Id
vt = BV True
vf = BV False

vunit :: Expr Id
vunit = Unit

infixl 9 @
(@) :: Expr Id -> Expr Id -> Expr Id
(@) = App

opcall :: Operation -> Expr Id -> Expr Id
opcall  = OpCall 

do_ :: Id -> Expr Id -> Expr Id -> Expr Id
do_ x c1 c2 = Do c1 x (abstract1 x c2)

(?*) :: Expr Id -> Expr Id -> Expr Id
(?*) = Pair

(<|) :: Expr Id -> Expr Id -> Expr Id
h <| c = With h c

handler :: Id -> Expr Id -> [(OpTag, Id, Id, Expr Id)] -> Expr Id
handler x e cases = Handler x (abstract1 x e) 
                            [(op, (x, k, abstract2 x k case')) | (op, x, k, case') <- cases]

inl :: Expr Id -> Expr Id
inl = InLorR True

inr :: Expr Id -> Expr Id
inr = InLorR False

unEither :: Expr Id -> (Id, Expr Id) -> (Id, Expr Id) -> Expr Id
unEither e (x, l) (y, r) = UnEither e x (abstract1 x l) y (abstract1 y r)

(?*>) :: Expr Id -> (Id, Id, Expr Id) -> Expr Id
(?*>) p (x, y, e) = Unpair p x y (abstract2 x y e)

hole i s = ExprHole i Nothing [ (E.BindVar x (0, 0) (0, 0), e) | (x, e) <- s ]

-- -- identity substitution
-- initSubst :: [Id] -> Subst Id
-- initSubst xs = Subst $ (\x -> (x, v x)) <$> xs

true = "f" ! "t" ! v"t"

testlambda = (eqnat @ n720 @ (add @ n703 @ n17))
  where
      false  = "f" ! "t" ! v"f"
      true   = "f" ! "t" ! v"t"
      iff    = "b" ! "t" ! "f" ! v"b" @ v"f" @ v"t"
      zero   = "z" ! "s" ! v"z"
      succ   = "n" ! "z" ! "s" ! v"s" @ v"n"
      one    = succ @ zero
      two    = succ @ one
      three  = succ @ two
      isZero = "n" ! v"n" @ true @ ("m" ! false)
      const  = "x" ! "y" ! v"x"
      pair   = "a" ! "b" ! "p" ! v"p" @ v"a" @ v"b"
      fst    = "ab" ! v"ab" @ ("a" ! "b" ! v"a")
      snd    = "ab" ! v"ab" @ ("a" ! "b" ! v"b")
      -- fix    = r $ "g" ! ("x" ! v"g"@ (v"x"@v"x")) @ ("x" ! v"g"@ (v"x"@v"x"))
      fix    = "f" ! ("x" ! v"f" @ ("v" ! v"x" @ v"x" @ v"v"))
                      @ ("x" ! v"f" @ ("v" ! v"x" @ v"x" @ v"v"))
      add    = fix @ ("radd" ! "x" ! "y" ! v"x" @ v"y" @ ("n" ! succ @ (v "radd" @ v"n" @ v"y")))
      mul    = fix @ ("rmul" ! "x" ! "y" ! v"x" @ zero @ ("n" ! add @ v"y" @ (v "rmul" @ v"n" @ v"y")))
      fac    = fix @ ("rfac" ! "x" ! v"x" @ one @ ("n" ! mul @ v"x" @ (v "rfac" @ v"n")))
      eqnat  = fix @ ("reqnat" ! "x" ! "y" ! v"x" @ (v"y" @ true @ (const @ false)) @ ("x1" ! v"y" @ false @ ("y1" ! v "reqnat" @ v"x1" @ v"y1")))
      sumto  = fix @ ("rsumto" ! "x" ! v"x" @ zero @ ("n" ! add @ v"x" @ (v"rsumto" @ v"n")))
      n5     = add @ two @ three
      n6     = add @ three @ three
      n17    = add @ n6 @ (add @ n6 @ n5)
      n37    = succ @ (mul @ n6 @ n6)
      n703   = sumto @ n37
      n720   = fac @ n6

testEval :: Spec
testEval = describe "eval" $ do
             it "can be used as UTLC" $ do
               runEval testlambda `shouldBe` Right true

values :: [Expr Id]
values =
  [ BV True,
    NV 1,
    Unit,
    Pair vt vt,
    handler "x" (v "x") [("op", "x", "k", v "k" @ v "x")],
    "x" ! v "x" @ v "y"
  ]

nonValues :: [Expr Id]
nonValues = 
  [ v"x",
    v"f" @ v"x",
    If (v"b") (v"t") (v"f"),
    OpCall (Operation "op") (v"v"),
    With (handler "x" (v "x") [("op", "x", "k", v "k" @ v "x")]) (v"c"),
    do_ "x" (v"c") (v"d"),
    v"p" ?*> ("x", "y", v"e")
  ]

testIsValue :: Spec
testIsValue = describe "isValue" $ do
  it "correctly identifies values" $ do
    map isValue values `shouldBe` replicate (length values) True
  it "correctly identifies non-values" $ do
    map isValue nonValues `shouldBe` replicate (length nonValues) False

testDecompose :: Spec
testDecompose = 
  describe "decompose" $ do
    it "doesn't decompose' a value" $ do
      map decompose' values `shouldBe` replicate (length values) (Right Nothing)
    let redexe1 = ("x"!v"x") @ vt
        redex1 = RApp ("x"!v"x") vt
        redexe2 = If vt vt vf
        redex2 = RIf vt vt vf
        redexe3 = (vt ?* vf) ?*> ("x", "y", v"x")
        redex3 = RUnPair (vt ?* vf) "x" "y" (abstract2 "x" "y" (v"x"))
        redexe4 = do_ "x" vt (v"x")
        redex4 = RDo vt "x" (abstract1 "x" (v"x"))
        redexes = [(redexe1, redex1), (redexe2, redex2), (redexe3, redex3), (redexe4, redex4)]

    it "decomposes regular redexes" $ do
      mapM_ (\(redexe, redex) -> decompose' redexe `shouldBe` Right (Just (H, Redex redex))) redexes

    it "decomposes nested redexes" $ do
      mapM_ (\(redexe, redex) -> decompose' (Pair redexe vt) `shouldBe` Right (Just (PairL H vt, Redex redex))) redexes
      mapM_ (\(redexe, redex) -> decompose' (Pair vt redexe) `shouldBe` Right (Just (PairR vt H, Redex redex))) redexes
      mapM_ (\(redexe, redex) -> decompose' (If redexe vt vf) `shouldBe` Right (Just (IfC H vt vf, Redex redex))) redexes
      mapM_ (\(redexe, redex) -> decompose' (OpCall (Operation "op") redexe) `shouldBe` Right (Just (OpCallE (Operation "op") H, Redex redex))) redexes
      mapM_ (\(redexe, redex) -> decompose' (App redexe vt) `shouldBe` Right (Just (AppL H vt, Redex redex))) redexes
      mapM_ (\(redexe, redex) -> decompose' (App vt redexe) `shouldBe` Right (Just (AppR vt H, Redex redex))) redexes

    it "decomposes operation calls" $ do
      decompose' (OpCall (Operation "op") true) `shouldBe` Right (Just (H, ROpCall (Operation "op") true))
      decompose' (Pair (OpCall (Operation "op") true) vt) `shouldBe` Right (Just (PairL H vt, ROpCall (Operation "op") true))
      decompose' (handler "x" (v "x") [] <| OpCall (Operation "op") true) 
        `shouldBe` Right (Just (WithB (handler "x" (v "x") []) H, ROpCall (Operation "op") true))

    it "decomposes handler redexes" $ do
      let handlerRedexe = handler "x" (v "x") [("op", "x", "k", v "k" @ v "x")] <| opcall (Operation "op") vt
          handlerRedex = RWith (handler "x" (v "x") [("op", "x", "k", v "k" @ v "x")]) H (opcall (Operation "op") vt)
          handlerRedexe2 = handler "x" (v "x") [("op", "x", "k", v "k" @ v "x")] <| vt
          handlerRedex2 = RWith (handler "x" (v "x") [("op", "x", "k", v "k" @ v "x")]) H vt
      decompose' handlerRedexe `shouldBe` Right (Just (H, Redex handlerRedex))
      decompose' handlerRedexe2 `shouldBe` Right (Just (H, Redex handlerRedex2))

    it "opcall propagates out" $ do
      let opcallRedexe = handler "x" (v"x") [("op", "x", "k", v "k" @ v "x")]
                            <| (handler "x" (v "x") [] <| opcall (Operation "op") vt)
          opcallRedex = RWith (handler "x" (v"x") [("op", "x", "k", v "k" @ v "x")]) 
                            (WithB (handler "x" (v "x") []) H)
                            (opcall (Operation "op") vt)
      decompose' opcallRedexe `shouldBe` Right (Just (H, Redex opcallRedex))

testState' = With h c @ NV 1
  where
    h = handler "x" ("s" ! Pair (v"x") (v"s"))
               [ ("get", "_", "k", "s" ! (v"k" @ hole 1 [] @ hole 2 []))
               , ("put", "v", "k", "s" ! (v"k" @ hole 3 [] @ hole 4 []))
               ]
    c = do_ "x" (OpCall (Operation "put") (NV 42))
               (OpCall (Operation "get") Unit)

testExample :: Spec
testExample = describe "example test case" $ do
  it "evaluates the state example correctly" $ do
    runEval testState' `shouldBe` Right (Pair (hole 1 []) (hole 2 []))
  it "substitute correctly" $ do
    runEval (("f" ! ("x" ! v"f" @ ("v" ! v"v") @ ("y" ! v"f" @ NV 1))) @ NV 2) `shouldBe` 
      Right ("x" ! NV 2 @ ("v" ! v"v") @ ("y" ! NV 2 @ NV 1))
    -- (\f. (\x . f (\v.v) (\y. f 1))) 2
  it "eval if correctly" $ do
    runEval (If vt vt vf) `shouldBe` Right vt
    runEval (If vf vt vf) `shouldBe` Right vf
    runEval (If (BiOp Eqi (NV 1) (NV 1)) vt vf) `shouldBe` Right vt
    runEval (BiOp Lt (NV 1) (NV 2)) `shouldBe` Right vt
    runEval (BiOp Le (NV 2) (NV 2)) `shouldBe` Right vt
    runEval (BiOp Gt (NV 3) (NV 2)) `shouldBe` Right vt
    runEval (BiOp Ge (NV 3) (NV 3)) `shouldBe` Right vt
    runEval (BiOp Neq (NV 1) (NV 2)) `shouldBe` Right vt
    runEval (fix @ fact @ NV 5) `shouldBe` Right (NV 120)
  it "eval expr with holes" $ do
    runEval (hole 1 [("x", v "x")]) `shouldBe` Right (hole 1 [("x", v "x")])
    runEval (BiOp Add (hole 1 [("x", v "x")]) (NV 1)) `shouldBe` Right (BiOp Add (hole 1 [("x", v "x")]) (NV 1))
    runEval (hole 1 [("x", v "x")] @ vt) `shouldBe` Right (hole 1 [("x", v "x")] @ vt)
    runEval (h <| opcall (Operation "log") (hole 1 [])) `shouldBe` Right (vunit ?* BiOp Add (NV 0) (hole 1 []))
    -- runEval (h <| do_ "_" (opcall (Operation "log") (hole 1 []))
    --                   vt) `shouldBe` Right (vunit ?* BiOp Add (NV 0) (hole 1 []))
    runEval (h <| do_ "_" (opcall (Operation "log") (hole 1 []))
                      (opcall (Operation "log") (hole 2 []))) 
        `shouldBe` Right (vunit ?* ((NV 0 ?+ hole 2 []) ?+ hole 1 []))
  it "operation calls propagate out of handlers" $ do
    runEval (h <| (h2 <| opcall (Operation "log") (NV 1))) `shouldBe` Right ((vunit ?* NV 0) ?* NV 1)
    runEval (h <| (h2 <| opcall (Operation "log2") (NV 1))) `shouldBe` Right ((vunit ?* NV 1) ?* NV 0)
  where
      fix = "f" ! ("x" ! v"f" @ ("v" ! v"x" @ v"x" @ v"v")) @ ("x" ! v"f" @ ("v" ! v"x" @ v"x" @ v"v"))
      fact = "fact" ! "n" ! If (BiOp Eqi (v "n") (NV 0)) (NV 1) (BiOp Mul (v"n") (v "fact" @ BiOp Sub (v"n") (NV 1)))
      h = handler "x" (v"x" ?* NV 0) [
          (OpTag "log", "a", "k", v"k" @ vunit ?*> ("x", "acc", v"x" ?* (v"acc" ?+ v"a")))
        ]
      h2 = handler "x" (v"x" ?* NV 0) [
          (OpTag "log2", "a", "k", v"k" @ vunit ?*> ("x", "acc", v"x" ?* (v"acc" ?+ v"a")))
        ]
      (?+) = BiOp Add

testPrettyFocusedConsistency :: Spec
testPrettyFocusedConsistency = describe "step-focused pretty consistency" $ do
  let samples =
        [ (("x" ! v "x") @ (NV 1), "beta")
        , (If (BiOp Eqi (NV 1) (NV 1)) (NV 10) (NV 20), "if")
        , (do_ "x" (NV 1) (BiOp Add (v "x") (NV 2)), "do")
        , (testState', "handler")
        , (BiOp Add (NV 1) (BiOp Mul (NV 2) (NV 3)), "biop-nested")
        , (("id" ! v "id") @ If (BiOp Eqi (NV 1) (NV 1)) (NV 2) (NV 3), "app-arg-if")
        , (Unpair (Pair (BiOp Add (NV 1) (NV 2)) (NV 4)) "x" "y" (abstract2 "x" "y" (BiOp Mul (v "x") (v "y"))), "unpair-nested")
        , (UnCons (Cons (BiOp Add (NV 1) (NV 2)) Nil) (NV 0) "x" "xs" (abstract2 "x" "xs" (v "x")), "uncons-nested")
        , (unEither (inl (BiOp Add (NV 1) (NV 2))) ("x", v "x") ("y", NV 0), "uneither-nested")
        , (hLog <| opcall (Operation "log") (BiOp Add (NV 1) (NV 2)), "with-handler-op")
        ]
      hLog =
        handler
          "x"
          (v "x")
          [(OpTag "log", "a", "k", v "k" @ v "a")]
  mapM_ (\(expr, label) ->
    it ("matches focused rendering with prettyShow for " ++ label) $ do
      case runEvalWithSteps expr of
        Left err -> expectationFailure ("evaluation failed unexpectedly: " ++ err)
        Right (_, steps) -> do
          steps `shouldSatisfy` (not . null)
          mapM_
            (\step -> do
              let (rendered, range) = prettyShowStepFocusedWithRange step
                  expected = prettyShow (stepFocusedExpr step)
              rendered `shouldBe` expected
              isJust range `shouldBe` True
            )
            steps
    ) samples

testUnEither :: Spec
testUnEither = describe "UnEither" $ do
  it "evaluates inl" $ do
    runEval (unEither (inl (NV 1)) ("x", v "x") ("y", NV 0)) `shouldBe` Right (NV 1)
  it "evaluates inr" $ do
    runEval (unEither (inr (NV 2)) ("x", NV 0) ("y", v "y")) `shouldBe` Right (NV 2)
  it "evaluates nested UnEither" $ do
    runEval (unEither (inl (inl (NV 3))) ("x", unEither (v "x") ("y", v "y") ("z", NV 0)) ("w", NV 1)) `shouldBe` Right (NV 3)

testLetRec :: Spec
testLetRec = describe "letrec" $ do
  it "evaluates recursive factorial function" $ do
    let body = If (BiOp Eqi (v "x") (NV 0))
                  (NV 1)
                  (BiOp Mul (v "x") (v "f" @ BiOp Sub (v "x") (NV 1)))
        c2 = v "f" @ NV 5
        expr = LetRec "f" "x" (abstract2 "f" "x" body) (abstract1 "f" c2)
    runEval expr `shouldBe` Right (NV 120)

testNorm :: Spec
testNorm = describe "normalization" $ do
  it "reduces simple redexes" $ do
    norm 100 (("x" ! v "x") @ v "y") `shouldBe` Just (v "y")
    norm 100 (("x" ! v "x") @ (("y" ! v "y") @ v "z")) `shouldBe` Just (v "z")

  it "reduces under binders" $ do
    norm 100 ("z" ! (("x" ! v "x") @ v "z")) `shouldBe` Just ("z" ! v "z")
    norm 100 ("z" ! (("x" ! v "x") @ v "y")) `shouldBe` Just ("z" ! v "y")

  it "keeps binder wrappers in norm steps" $ do
    let expr =
          "x"
            ! unEither
              (inr (NV 1))
              ("l", BiOp Add (v "l") (NV 1))
              ("r", BiOp Add (v "r") (NV 2))
        expectedMid = "x" ! BiOp Add (NV 1) (NV 2)
        expectedFinal = "x" ! NV 3
        (res, steps) = normWithSteps 2 expr
    res `shouldBe` Right expectedFinal
    case steps of
      [s0, s1] -> do
        stepBefore s0 `shouldBe` expr
        stepAfter s0 `shouldBe` Just expectedMid
        stepBefore s1 `shouldBe` expectedMid
        stepAfter s1 `shouldBe` Just expectedFinal
      _ -> expectationFailure "expected exactly 2 normalization steps"
    
  it "reduces if expressions" $ do
    norm 100 (If vt (v "x") (v "y")) `shouldBe` Just (v "x")
    norm 100 (If vf (v "x") (v "y")) `shouldBe` Just (v "y")
    norm 100 (If (BiOp Eqi (NV 1) (NV 1)) (v "x") (v "y")) `shouldBe` Just (v "x")
    -- condition is open/stuck
    norm 100 (If (v "c") (("x" ! v "x") @ v "t") (v "f")) `shouldBe` Just (If (v "c") (v "t") (v "f"))


  it "reduces binary operations" $ do
    norm 100 (BiOp Add (NV 1) (NV 2)) `shouldBe` Just (NV 3)
    norm 100 (BiOp Add (v "x") (BiOp Add (NV 1) (NV 2))) `shouldBe` Just (BiOp Add (v "x") (NV 3))
    
  it "reduces unpair" $ do
    norm 100 (Unpair (Pair (v "a") (v "b")) "x" "y" (abstract2 "x" "y" (v "x"))) `shouldBe` Just (v "a")
    norm 100 (Unpair (v "p") "x" "y" (abstract2 "x" "y" (("z" ! v "z") @ v "x"))) 
      `shouldBe` Just (Unpair (v "p") "x" "y" (abstract2 "x" "y" (v "x")))

  it "reduces uncons" $ do
    norm 100 (UnCons (Cons (v "h") (v "t")) (v "nil") "x" "xs" (abstract2 "x" "xs" (v "x"))) `shouldBe` Just (v "h")
    norm 100 (UnCons Nil (v "nil") "x" "xs" (abstract2 "x" "xs" (v "x"))) `shouldBe` Just (v "nil")
    norm 100 (UnCons (v "l") (v "nil") "x" "xs" (abstract2 "x" "xs" (("z" ! v "z") @ v "x")))
      `shouldBe` Just (UnCons (v "l") (v "nil") "x" "xs" (abstract2 "x" "xs" (v "x")))
      
  it "reduces uneither" $ do
    norm 100 (unEither (inl (v "a")) ("x", v "x") ("y", v "y")) `shouldBe` Just (v "a")
    norm 100 (unEither (inr (v "b")) ("x", v "x") ("y", v "y")) `shouldBe` Just (v "b")
    norm 100 (unEither (v "e") ("x", ("z" ! v "z") @ v "x") ("y", v "y"))
      `shouldBe` Just (unEither (v "e") ("x", v "x") ("y", v "y"))

  it "reduces letrec" $ do
    -- Let's test a simple unfolding
    -- letrec f x = x in f y --> y
    let body = v "x"
        c2 = v "f" @ v "y" 
        term = LetRec "f" "x" (abstract2 "f" "x" body) (abstract1 "f" c2)
    norm 100 term `shouldBe` Just (v "y")

  it "won't unfold forever" $ do
    -- letrec f x = f x in f y --> f y (doesn't keep unfolding)
    let body = v "f" @ v "x"
        c2 = v "f"
        term = LetRec "f" "x" (abstract2 "f" "x" body) (abstract1 "f" c2)
    norm 100 term `shouldBe` Nothing

  it "reduces handlers" $ do
    let h = handler "eff" (v "eff") [("op", "x", "k", v "k" @ (v "x"))]
    -- shallow handler, handles op
    norm 100 (h <| opcall (Operation "op") (v "val")) `shouldBe` Just (v "val")
    
    -- deep handler test
    let hAdd = handler "eff" (v "eff") [("op", "x", "k", v "k" @ (BiOp Add (v "x") (NV 1)))]
    norm 100 (hAdd <| opcall (Operation "op") (NV 1)) `shouldBe` Just (NV 2)

  it "renames" $ do
    -- \x. (\y. \x. y) x should be \x. \x1. x
    norm 100 ("x" ! ("y" ! ("x" ! v "y")) @ v "x") `shouldBe` Just ("x" ! ("x'" ! v "x"))
    norm 100 ("x" ! ("y" ! ("x" ! hole 1 [("x", v "x"), ("y", v "y")])) @ v "x") `shouldBe` 
      Just (Abs "x" (Scope (Abs "x'" 
        (Scope (hole 1 [("x'", Var (B ())), ("y", Var (F (Var (B ()))))])))))
