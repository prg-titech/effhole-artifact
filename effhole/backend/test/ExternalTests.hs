{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}

module ExternalTests (testElaboration) where

import External
import qualified Internal as I
import Elaboration
import Bound
import Test.Hspec 

-- printRes :: (Either String (CompType, I.Computation Id), String) -> IO ()
-- printRes (Left s1, s2) = do
--   putStrLn $ "Failed with msg: " ++ s1
--   putStrLn "With log:"
--   putStrLn s2
-- printRes (Right (ct, c), s2) = do
--   putStrLn "Succeeded"
--   putStrLn $ "inferred type: " ++ show ct
--   putStrLn "internal term: "
--   print c
--   putStrLn "With log:"
--   putStrLn s2
  
-- tp = App (Abs "x" (OpCall (Operation "print") (ValueHole 1))) (NV 1)
-- testh = Handler "x" (Ret (Var "x"))
--         [HandlerCase "print" "x" "k" (CompHole 1)]

-- -- the original testcase, but it doesn't check
-- test0 = With testh (OpCall (Operation "print") (NV 1))
-- -- annotated the wrapped handler
-- test = Do "x" (Ret testh) $ With (Var "x") (OpCall (Operation "print") (NV 1))
-- -- annotate the handler directly
-- test' = With testh (OpCall (Operation "print") (NV 1))

-- test2 = Do "x" (Ret testh) 
--        $ Do "" (With (Var "x") (OpCall (Operation "print") (NV 1)))
--          (With (Var "x") (OpCall (Operation "print") (NV 2)))

-- testState = Do "t" (With st c) (App (Var "t") (NV 1))
--   where
--     st = Handler "x" (Ret (Abs "s" (Ret (Var "x"))))
--                [ HandlerCase "get" "_" "k" (Ret (Abs "s"
--                                              (Do "t" (App (Var "k") (ValueHole 1))
--                                               (App (Var "t") (ValueHole 2)))))
--                , HandlerCase "put" "s" "k" (CompHole 3)]
--     c = Do "x" (OpCall (Operation "get") Unit) 
--                (OpCall (Operation "put") (Var "x"))
 
-- testState' = Do "t" (With st c) (App (Var "t") (NV 1))
--   where
--     st = Handler "x" (Ret (Abs "s" (Ret (Pair (Var "x") (Var "s")))))
--                [ HandlerCase "get" "_" "k" (Ret (Abs "s"
--                                              (Do "t" (App (Var "k") (ValueHole 1))
--                                               (App (Var "t") (ValueHole 2)))))
--                , HandlerCase "put" "v" "k" (Ret (Abs "s"
--                                              (Do "t" (App (Var "k") (ValueHole 3))
--                                               (App (Var "t") (ValueHole 4)))))
--                ]
--     c = Do "x" (OpCall (Operation "put") (NV 42)) 
--                (OpCall (Operation "get") Unit)

-- elabRes :: Computation -> I.Computation Id
-- elabRes = elaborate S.empty 

-- doEval' :: I.Computation Id -> IO (I.Computation Id)
-- doEval' c = d' c
--   where
--     d' c = do
--         print c
--         putStrLn "----"
--         case I.evalStepC freshnames c of
--             Nothing -> return c
--             Just c' -> d' c' 

-- -- whole program testcases
-- testProgram :: Spec
-- testProgram = describe "whole program test cases" $ do
--                 it "annotation on value and computation should be the same" $ do
--                   let f = show . I.eval . elabRes
--                   f test `shouldBe` f test'

-- testType' = App (Abs "x" (Ret (Var "x")) ) (Abs "x" (Ret (Var "x")))
  
-- stateRes = I.eval $ elabRes testState
-- x' = I.eval $ elabRes testType'

bv line x = BindVar x (line, 1) (line, 2)

testElaboration :: Spec
testElaboration = describe "elaboration" $ do
  it "deduplicates hole captures by keeping the nearest binding" $ do
    let expr = Do [ DoBind (bv 1 "x") (NV 1)
                  , DoBind (bv 2 "v") (ExprHole 1)
                  , DoBind (bv 3 "x") (NV 2)
                  ] (ExprHole 2)
        expected =
          I.Do (I.NV 1) "x" (abstract1 "x"
            (I.Do (I.ExprHole 1 Nothing [(bv 1 "x", I.Var "x")]) "v" (abstract1 "v"
              (I.Do (I.NV 2) "x" (abstract1 "x"
                (I.ExprHole 2 Nothing [(bv 3 "x", I.Var "x"), (bv 2 "v", I.Var "v")]))))))
    elaborate expr `shouldBe` expected