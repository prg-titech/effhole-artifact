{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import External
import Elaboration
import qualified Internal as I
import Server
import CLI

bv x = BindVar x (0, 0) (0, 0)

-- testState' = Do "t" (With st c) (App (Var "t") (NV 1))
--   where
--     st = Handler "x" (Abs "s" (Pair (Var "x") (Var "s")))
--                [ HandlerCase "get" "_" "k" (Abs "s"
--                                              (Do "t" (App (Var "k") (ExprHole 1))
--                                               (App (Var "t") (ExprHole 2))))
--                , HandlerCase "put" "v" "k" (Abs "s"
--                                              (Do "t" (App (Var "k") (ExprHole 3))
--                                               (App (Var "t") (ExprHole 4))))
--                ]
--     c = Do "x" (OpCall (Operation "put") (NV 42)) 
--                (OpCall (Operation "get") Unit)

testState' = App (With h c) (NV 1)
  where
    h = Handler (bv "x") (Abs (bv "s") [] (Pair (Var "x") (Var "s")))
               [ HandlerCase "get" (bv "_") (bv "k") 
                  (Abs (bv "s") [] (App (App (Var "k") (ExprHole 1)) (ExprHole 2)))
               , HandlerCase "put" (bv "v") (bv "k") 
                  (Abs (bv "s") [] (App (App (Var "k") (ExprHole 3)) (ExprHole 4)))
               ]
    c = Do [DoBind (bv "x") (OpCall (Operation "put") (NV 42))] 
            (OpCall (Operation "get") Unit)


testDo1 = Do [DoBind (bv "x") (Do [DoBind (bv "y") (OpCall (Operation "put") (NV 42))] 
                (OpCall (Operation "get") Unit)),
               DoExpr (OpCall (Operation "put") (NV 43)),
            DoBind (bv "z") (OpCall (Operation "get") Unit)] 
           (OpCall (Operation "get") Unit)
   
main :: IO ()
main = cli
--   let internalExpr = elaborate testDo1
--   putStrLn $ I.prettyShow internalExpr
-- --   print $ I.eval' internalExpr
-- --   I.eval' internalExpr
-- --   putRes testState'