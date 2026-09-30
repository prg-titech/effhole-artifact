{-# LANGUAGE OverloadedStrings #-}

import ExternalTests
import InternalTests
import ParserTests
import Test.Hspec (hspec)

testCases :: IO ()
-- testCases = mapM_ hspec [testEval, testProgram]
testCases = mapM_ hspec $ [testEval, testIsValue, testDecompose, testExample, testPrettyFocusedConsistency, testUnEither, testLetRec, testNorm, testElaboration] ++ testParser

main :: IO ()
main = do
  testCases
  -- printRes (elabRes testState')
  -- doEval' (elabRes testState')
  -- let res = VCast (NV 1) ValueHoleType (ValueHoleType :-> comphole0)
  -- case res of
  --   v@(VCast v1 t1 t2) -> do
  --     print v1
  --     print t1
  --     print t2
  --     print (evalStepV v)
  --   _ -> undefined

  return ()
