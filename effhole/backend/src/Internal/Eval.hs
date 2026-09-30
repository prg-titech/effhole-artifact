{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}

module Internal.Eval where

import Bound
import Common
import Control.Applicative
import Control.Monad (when)
import Control.Monad.Except
import Control.Monad.IO.Class
import Control.Monad.Reader (Reader, asks, local, runReader, MonadReader)
import Control.Monad.State.Strict (State, execState, gets, modify')
import Control.Monad.Writer
import Control.Monad.Writer.Class
import qualified Data.Text as T
import Internal.Pretty
import Internal.Syntax
import Prettyprinter
import Type

data Step a = Step
  { stepBefore :: Expr a,
    stepContext :: ECtx a,
    stepFocus :: RedexOrOpCall a,
    stepAfter :: Maybe (Expr a)
  }
  deriving (Show, Eq)

redexExpr :: Redex a -> Expr a
redexExpr (RApp e1 e2) = App e1 e2
redexExpr (RBiOp op e1 e2) = BiOp op e1 e2
redexExpr (RUnCons e1 e2 x k scope) = UnCons e1 e2 x k scope
redexExpr (RIf e1 e2 e3) = If e1 e2 e3
redexExpr (RUnPair e a b scope) = Unpair e a b scope
redexExpr (RUnEither e x le y re) = UnEither e x le y re
redexExpr (RWith h ctx e) = With h (withContext ctx e)
redexExpr (RDo e x scope) = Do e x scope
redexExpr (RLetRec f x s1 s2) = LetRec f x s1 s2

focusExpr :: RedexOrOpCall a -> Expr a
focusExpr (Redex r) = redexExpr r
focusExpr (ROpCall op e) = OpCall op e

stepFocusedExpr :: Step a -> Expr a
stepFocusedExpr step = withContext (stepContext step) (focusExpr (stepFocus step))

recordStep :: (MonadWriter [Step Id] m) => Expr Id -> ECtx Id -> RedexOrOpCall Id -> Maybe (Expr Id) -> m ()
recordStep before ctx focus after = tell [Step before ctx focus after]

data DecomposeCtx = DecomposeCtx 
  { _isValue      :: Expr Id -> Bool 
  , _isFinal      :: Expr Id -> Bool 
  , _isRetHandled :: Expr Id -> Bool 
  }

decomposeReduceWith :: (MonadError String m) => DecomposeCtx -> Expr Id -> m (Maybe (ECtx Id, RedexOrOpCall Id, Maybe (Expr Id)))
decomposeReduceWith dctx e = do
  res <- decomposeWith dctx e
  case res of
    Nothing -> return Nothing
    Just (ctx, focus) -> case focus of
      Redex redex -> do
        next <- withContext ctx <$> reduceWith dctx redex
        return $ Just (ctx, focus, Just next)
      ROpCall _ _ -> return $ Just (ctx, focus, Nothing)

domain :: Expr a -> [OpTag]
domain (Handler _ _ cases) = [op | (op, (_, _, _)) <- cases]
domain _ = error "domain is only defined for handlers"

isValue :: Expr a -> Bool
isValue (BV _) = True
isValue (NV _) = True
isValue (Str _) = True
isValue Unit = True
isValue Nil = True
isValue (Cons e1 e2) = isValue e1 && isValue e2
isValue (Abs _ _) = True
isValue (Pair e1 e2) = isValue e1 && isValue e2
isValue (InLorR _ e) = isValue e
isValue Handler {} = True
isValue _ = False

isPureHole :: Expr a -> Bool
isPureHole ExprHole{} = True
isPureHole _ = False

isRetHandled :: Expr a -> Bool
isRetHandled x = isValue x || isPureHole x

isIndet :: Expr a -> Bool
isIndet (BiOp _ e1 e2) = isFinal e1 && isIndet e2 || isIndet e1 && isFinal e2
isIndet (Cons e1 e2) = isFinal e1 && isIndet e2 || isIndet e1 && isFinal e2
isIndet (UnCons Cons {} _ _ _ _) = False
isIndet (UnCons l _ _ _ _) = isIndet l
isIndet (Pair e1 e2) = isFinal e1 && isIndet e2 || isIndet e1 && isFinal e2
isIndet (InLorR _ e) = isIndet e
isIndet (UnEither e _ _ _ _) = isIndet e
isIndet ExprHole {} = True
isIndet (App f _) = isIndet f
isIndet (If b _ _) = isIndet b
isIndet (Unpair Pair {} _ _ _) = False
isIndet (Unpair p _ _ _) = isIndet p
-- with h e is stuck by a hole iff:
-- h is indet, or e is indet and it cannot be handled by the return clause
isIndet (With h e) = isFinal h && (isIndet e && not (isRetHandled e))
                  || isIndet h && isFinal e
isIndet _ = False

isFinal :: Expr a -> Bool
isFinal e = isValue e || isIndet e

evalDecomposeCtx :: DecomposeCtx
evalDecomposeCtx = DecomposeCtx isValue isFinal isRetHandled

-- the evaluation context for evaluation
-- denotes the position of the redex in the expression
data ECtx a
  = H
  | BiOpL ArithOp (ECtx a) (Expr a)
  | BiOpR ArithOp (Expr a) (ECtx a)
  | ConsL (ECtx a) (Expr a)
  | ConsR (Expr a) (ECtx a)
  | UnConsP (ECtx a) (Expr a) Id Id (Scope XOrK Expr a)
  | PairL (ECtx a) (Expr a)
  | PairR (Expr a) (ECtx a)
  | InLorRI Bool (ECtx a) -- True for left, False for right
  | UnEitherP (ECtx a) Id (Scope () Expr a) Id (Scope () Expr a)
  | AppL (ECtx a) (Expr a)
  | AppR (Expr a) (ECtx a)
  | IfC (ECtx a) (Expr a) (Expr a)
  | UnPairP (ECtx a) Id Id (Scope XOrK Expr a)
  | OpCallE Operation (ECtx a)
  | WithH (ECtx a) (Expr a)
  | WithB (Expr a) (ECtx a)
  | Do1 (ECtx a) Id (Scope () Expr a)
  deriving (Show, Eq)

-- a context is also a continuation
toCont :: ECtx a -> Scope () Expr a
toCont H = Scope $ Var (B ())
toCont (BiOpL op ctx e2) = toScope $ BiOp op (fromScope $ toCont ctx) (F <$> e2)
toCont (BiOpR op e1 ctx) = toScope $ BiOp op (F <$> e1) (fromScope $ toCont ctx)
toCont (ConsL ctx e2) = toScope $ Cons (fromScope $ toCont ctx) (F <$> e2)
toCont (ConsR e1 ctx) = toScope $ Cons (F <$> e1) (fromScope $ toCont ctx)
toCont (UnConsP ctx e2 x k scope) = toScope $ UnCons (fromScope $ toCont ctx) (F <$> e2) x k (fmap F scope)
toCont (PairL ctx e2) = toScope $ Pair (fromScope $ toCont ctx) (F <$> e2)
toCont (PairR e1 ctx) = toScope $ Pair (F <$> e1) (fromScope $ toCont ctx)
toCont (InLorRI b ctx) = toScope $ InLorR b (fromScope $ toCont ctx)
toCont (UnEitherP ctx x le y re) = toScope $ UnEither (fromScope $ toCont ctx) x (fmap F le) y (fmap F re)
toCont (AppL ctx e2) = toScope $ App (fromScope $ toCont ctx) (F <$> e2)
toCont (AppR e1 ctx) = toScope $ App (F <$> e1) (fromScope $ toCont ctx)
toCont (IfC ctx e2 e3) = toScope $ If (fromScope $ toCont ctx) (F <$> e2) (F <$> e3)
toCont (UnPairP ctx a b scope) = toScope $ Unpair (fromScope $ toCont ctx) a b (fmap F scope)
toCont (OpCallE op ctx) = toScope $ OpCall op (fromScope $ toCont ctx)
toCont (WithH ctx e2) = toScope $ With (fromScope $ toCont ctx) (F <$> e2)
toCont (WithB e1 ctx) = toScope $ With (F <$> e1) (fromScope $ toCont ctx)
toCont (Do1 ctx x scope) = toScope $ Do (fromScope $ toCont ctx) x (fmap F scope)

boundOps :: ECtx a -> [OpTag]
boundOps H = []
boundOps (BiOpL _ ctx _) = boundOps ctx
boundOps (BiOpR _ _ ctx) = boundOps ctx
boundOps (ConsL ctx _) = boundOps ctx
boundOps (ConsR _ ctx) = boundOps ctx
boundOps (UnConsP ctx _ _ _ _) = boundOps ctx
boundOps (PairL ctx e2) = boundOps ctx
boundOps (PairR e1 ctx) = boundOps ctx
boundOps (InLorRI _ ctx) = boundOps ctx
boundOps (UnEitherP ctx _ _ _ _) = boundOps ctx
boundOps (AppL ctx e2) = boundOps ctx
boundOps (AppR e1 ctx) = boundOps ctx
boundOps (IfC ctx e2 e3) = boundOps ctx
boundOps (UnPairP ctx a b scope) = boundOps ctx
boundOps (OpCallE op ctx) = boundOps ctx
boundOps (WithH ctx e2) = boundOps ctx
boundOps (WithB h ctx) = boundOps ctx ++ domain h
boundOps (Do1 ctx x scope) = boundOps ctx

-- given an evaluation context and an expression, plug the expression into the context to get a new expression
withContext :: ECtx a -> Expr a -> Expr a
withContext H e = e
withContext (BiOpL op ctx e2) e = BiOp op (withContext ctx e) e2
withContext (BiOpR op e1 ctx) e = BiOp op e1 (withContext ctx e)
withContext (ConsL ctx e2) e = Cons (withContext ctx e) e2
withContext (ConsR e1 ctx) e = Cons e1 (withContext ctx e)
withContext (UnConsP ctx e2 x k scope) e = UnCons (withContext ctx e) e2 x k scope
withContext (PairL ctx e2) e = Pair (withContext ctx e) e2
withContext (PairR e1 ctx) e = Pair e1 (withContext ctx e)
withContext (InLorRI b ctx) e = InLorR b (withContext ctx e)
withContext (UnEitherP ctx x le y re) e = UnEither (withContext ctx e) x le y re
withContext (AppL ctx e2) e = App (withContext ctx e) e2
withContext (AppR e1 ctx) e = App e1 (withContext ctx e)
withContext (IfC ctx e2 e3) e = If (withContext ctx e) e2 e3
withContext (UnPairP ctx a b scope) e = Unpair (withContext ctx e) a b scope
withContext (OpCallE op ctx) e = OpCall op (withContext ctx e)
withContext (WithH ctx e2) e = With (withContext ctx e) e2
withContext (WithB e1 ctx) e = With e1 (withContext ctx e)
withContext (Do1 ctx x scope) e = Do (withContext ctx e) x scope

data Redex a
  = RApp (Expr a) (Expr a) -- (Abs e) v
  | RBiOp ArithOp (Expr a) (Expr a) -- for example, 1 + 2
  | RUnCons (Expr a) (Expr a) Id Id (Scope XOrK Expr a) -- for example, uncons l { nil -> e1 | cons x xs -> e2 }
  | RIf (Expr a) (Expr a) (Expr a) -- if True/False then e2 else e3
  | RUnPair (Expr a) Id Id (Scope XOrK Expr a)
  | RUnEither (Expr a) Id (Scope () Expr a) Id (Scope () Expr a)
  | RWith (Expr a) (ECtx a) (Expr a) -- with h E[op(v)], it captures a continuation
  | RDo (Expr a) Id (Scope () Expr a) -- do v E[...]
  | RLetRec Id Id (Scope XOrK Expr a) (Scope () Expr a) -- letrec f x = e in e'
  deriving (Show, Eq)

data RedexOrOpCall a = Redex (Redex a) | ROpCall Operation (Expr a) deriving (Show, Eq)

-- it is used when you are sure a redex or opcall exists
getRedexOp :: (MonadError String m) => Expr Id -> m (ECtx Id, RedexOrOpCall Id)
getRedexOp e = do
  res <- decompose' e
  case res of
    Nothing -> internalError $ prettyShow e ++ " is not a value but cannot be decomposed further"
    Just res -> return res

guardWith :: (MonadError String m) => String -> Bool -> m ()
guardWith _ True = return ()
guardWith err False = throwError err

-- generic decomposeWith that allows customizing what is considered "Final" (stuck or value)
decomposeWith :: (MonadError String m) => DecomposeCtx -> Expr Id -> m (Maybe (ECtx Id, RedexOrOpCall Id))
decomposeWith (DecomposeCtx _isValue _isFinal _isRetHandled) = decomposeGen
  where
    -- Local getRedexOp that uses the recursive decompose
    getRedexOps (Var x) = throwError $ "Undefined variable: " ++ T.unpack x
    getRedexOps e = do
      res <- decomposeGen e
      case res of
        Nothing -> internalError $ prettyShow e ++ " is not a value but cannot be decomposed further"
        Just res -> return res

    decomposeGen (BiOp op e1 e2)
      | not (_isFinal e1) = do
          (ctx, e) <- getRedexOps e1
          return $ Just (BiOpL op ctx e2, e) -- eval left side first
      | not (_isFinal e2) = do
          (ctx, e) <- getRedexOps e2
          return $ Just (BiOpR op e1 ctx, e) -- then eval right side
      | _isValue e1 && _isValue e2 = return $ Just (H, Redex $ RBiOp op e1 e2) -- then evaluate the biop
      | otherwise = return Nothing -- if either side is indet, the whole expression is indet, no redex
    decomposeGen (Cons e1 e2)
      | not (_isFinal e1) = do
          (ctx, e) <- getRedexOps e1
          return $ Just (ConsL ctx e2, e) -- eval head first
      | not (_isFinal e2) = do
          (ctx, e) <- getRedexOps e2
          return $ Just (ConsR e1 ctx, e) -- then eval tail
      | otherwise = return Nothing -- cons is a value, no redex
    decomposeGen (UnCons e1 e2 x k scope)
      | not (_isFinal e1) = do
          (ctx, e) <- getRedexOps e1
          return $ Just (UnConsP ctx e2 x k scope, e) -- eval the scrutinee first
      | case e1 of Nil -> True; Cons {} -> True; _ -> False = return $ Just (H, Redex $ RUnCons e1 e2 x k scope) -- then evaluate uncons
      | _isValue e1 = throwError $ "eval error: uncons should be applied to a list, but got:\n" ++ prettyShow e1
      | otherwise = return Nothing -- if the scrutinee is indet, the whole expression is indet, no redex
    decomposeGen (Pair e1 e2)
      | not (_isFinal e1) = do
          (ctx, e) <- getRedexOps e1
          return $ Just (PairL ctx e2, e)
      | not (_isFinal e2) = do
          (ctx, e) <- getRedexOps e2
          return $ Just (PairR e1 ctx, e)
      | otherwise = return Nothing
    decomposeGen (InLorR b e)
      | not (_isFinal e) = do
          (ctx, e) <- getRedexOps e
          return $ Just (InLorRI b ctx, e)
      | otherwise = return Nothing
    decomposeGen (UnEither e x le y re)
      | not (_isFinal e) = do
          (ctx, e) <- getRedexOps e
          return $ Just (UnEitherP ctx x le y re, e)
      | case e of InLorR {} -> True; _ -> False = return $ Just (H, Redex $ RUnEither e x le y re)
      | _isValue e = throwError $ "eval error: uneither should be applied to an either, but got\n" ++ prettyShow e
      | otherwise = return Nothing -- if the scrutinee is indet, the whole expression is indet, no redex
    decomposeGen (App e1 e2)
      | not (_isFinal e1) = do
          (ctx, e) <- getRedexOps e1
          return $ Just (AppL ctx e2, e)
      | not (_isFinal e2) = do
          (ctx, e) <- getRedexOps e2
          return $ Just (AppR e1 ctx, e)
      | _isValue e1 = do
          -- all abstraction forms are values
          guardWith ("eval error: application should be a function, but got\n" ++ prettyShow e1 ++ " \napplied\n" ++ prettyShow e2) $
            case e1 of Abs {} -> True; _ -> False
          return $ Just (H, Redex $ RApp e1 e2)
      | otherwise = return Nothing -- if the function position is indet, the whole expression is indet, no redex
    decomposeGen (If e1 e2 e3)
      | not (_isFinal e1) = do
          (ctx, e) <- getRedexOps e1
          return $ Just (IfC ctx e2 e3, e)
      | _isValue e1 = do
          -- only boolean values can be conditions of if
          guardWith ("eval error: condition of if should be a boolean, but got:\n" ++ prettyShow e1) $
            case e1 of BV _ -> True; _ -> False
          return $ Just (H, Redex $ RIf e1 e2 e3)
      | otherwise = return Nothing -- if the condition is indet, the whole expression is indet, no redex
    decomposeGen (Unpair e a b scope)
      | not (_isFinal e) = do
          (ctx, e) <- getRedexOps e
          return $ Just (UnPairP ctx a b scope, e)
      | Pair _ _ <- e = return $ Just (H, Redex $ RUnPair e a b scope)
      | _isValue e = throwError $ "eval error: Unpair should be applied to a pair, but got:\n" ++ prettyShow e
      | otherwise = return Nothing -- if the scrutinee is indet, the whole expression is indet, no redex
    decomposeGen (OpCall op e)
      | not (_isFinal e) = do
          (ctx, e) <- getRedexOps e
          return $ Just (OpCallE op ctx, e) -- eval op(-) first
      | otherwise = return $ Just (H, ROpCall op e) -- then eval op
    decomposeGen (With e1 e2)
      | not (_isFinal e1) = do
          (ctx, e) <- getRedexOps e1
          return $ Just (WithH ctx e2, e)
      | not (_isFinal e2) = do
          (ctx, e) <- getRedexOps e2
          case e of
            ROpCall op v -> case op of
              Operation opTag ->
                if opTag `notElem` boundOps ctx -- only evaluate op calls that are not bound by the handler inside
                  && opTag `elem` domain e1 -- only evaluate op calls that are in the domain of the handler
                  then -- it is handled by the handler, return the term as the redex
                    return $ Just (H, Redex $ RWith e1 ctx (OpCall op v))
                  else -- it is not handled by the handler, return op call first
                    return $ Just (WithB e1 ctx, ROpCall op v)
              _ ->
                -- for op holes, it cannot be handled by the handler, return op call first
                return $ Just (WithB e1 ctx, ROpCall op v)
            Redex redex -> return $ Just (WithB e1 ctx, Redex redex)
      | _isValue e1 && _isRetHandled e2 = do
          guardWith ("eval error: with should be a handler, but got\n" ++ prettyShow e1) $
            case e1 of Handler {} -> True; _ -> False
          return $ Just (H, Redex $ RWith e1 H e2) -- with h v
      | otherwise = return Nothing -- if the handler is indet, the whole expression is indet, no redex
    decomposeGen (Do e x scope)
      | not (_isFinal e) = do
          (ctx, e) <- getRedexOps e
          return $ Just (Do1 ctx x scope, e)
      | otherwise = return $ Just (H, Redex $ RDo e x scope)
    decomposeGen (LetRec f x scope e) = return $ Just (H, Redex $ RLetRec f x scope e)
    decomposeGen _ = return Nothing

-- return the evaluation context and the redex or opcall if exists
-- otherwise return Nothing
decompose' :: (MonadError String m) => Expr Id -> m (Maybe (ECtx Id, RedexOrOpCall Id))
decompose' = decomposeWith evalDecomposeCtx

reduceWith :: (MonadError String m) => DecomposeCtx -> Redex Id -> m (Expr Id)
reduceWith _ (RApp (Abs _ e) v2) = return $ instantiate1 v2 e
reduceWith _ (RBiOp op e1 e2) = case (op, e1, e2) of
  (Add, NV n1, NV n2) -> return $ NV (n1 + n2)
  (Sub, NV n1, NV n2) -> return $ NV (n1 - n2)
  (Mul, NV n1, NV n2) -> return $ NV (n1 * n2)
  (Div, NV n1, NV n2) -> if n2 == 0 then throwError "division by zero" else return $ NV (n1 `div` n2)
  (Eqi, NV n1, NV n2) -> return $ BV (n1 == n2)
  (Neq, NV n1, NV n2) -> return $ BV (n1 /= n2)
  (Lt, NV n1, NV n2) -> return $ BV (n1 < n2)
  (Le, NV n1, NV n2) -> return $ BV (n1 <= n2)
  (Gt, NV n1, NV n2) -> return $ BV (n1 > n2)
  (Ge, NV n1, NV n2) -> return $ BV (n1 >= n2)
  (Concat, Str s1, Str s2) -> return $ Str (s1 ++ s2)
  -- TODO: better error message for type error
  _ -> throwError $
      "invalid redex: both operands of" ++ show op ++ " should be numbers, but got:\n"
        ++ prettyShow e1
        ++ " and "
        ++ prettyShow e2
reduceWith _ (RUnCons e1 e2 _ _ scope) = case e1 of
  Nil -> return e2
  Cons v1 v2 -> return $ instantiate2 v1 v2 scope
  _ -> throwError $ "invalid redex: uncons should be applied to a list, but got:\n" ++ prettyShow e1
reduceWith _ (RIf (BV True) e2 _) = return e2
reduceWith _ (RIf (BV False) _ e3) = return e3
reduceWith _ (RUnPair (Pair v1 v2) _ _ scope) = return $ instantiate2 v1 v2 scope
reduceWith _ (RUnEither (InLorR b v) _ le _ re) = return $ if b then instantiate1 v le else instantiate1 v re
reduceWith _ (RWith h@(Handler _ _ cases) ctx (OpCall op v)) = case op of
  Operation opTag -> case lookup opTag cases of
    Just (_, _, caseScope) ->
      let -- k = Abs (toCont ctx) -- shallow
          k = Abs dummy (toCont (WithB h ctx)) -- deep
       in return $ instantiate2 v k caseScope
    Nothing -> return $ withContext ctx (OpCall (Operation opTag) v)
  OpHole _ -> internalError $ "invalid redex:" ++ show op -- this should never happen
reduceWith dctx (RWith (Handler _ vcase _) H v) -- the surrounding context must be empty
  | _isRetHandled dctx v = return $ instantiate1 v vcase
  | otherwise = internalError $ "invalid redex: the body of with cannot be handled by the return clause: " ++ prettyShow v
reduceWith _ (RDo v _ scope) = return $ instantiate1 v scope
reduceWith _ (RLetRec f x s1 s2) = return $ instantiate1 t s2
  where
    -- letrec f x = c1 in c2 --> letrec f x = c1 in c2[f := \x. letrec f x = c1 in c1]
    t = Abs x (abstract1 x (LetRec f x s1 t'))
    t' = abstract1 f (instantiate2 (Var f) (Var x) s1)
reduceWith _ r = internalError $ "invalid redex:" ++ show r -- this should never happen, it is checked by the guard in decompose'

reduce :: (MonadError String m) => Redex Id -> m (Expr Id)
reduce = reduceWith evalDecomposeCtx

evalStep :: (MonadError String m) => Expr Id -> m (Maybe (Expr Id))
evalStep e = fst <$> runWriterT (evalStepWithSteps e)

evalStepWithSteps :: (MonadError String m, MonadWriter [Step Id] m) => Expr Id -> m (Maybe (Expr Id))
evalStepWithSteps e = do
  res <- decomposeReduceWith evalDecomposeCtx e
  case res of
    Nothing -> return Nothing
    Just (ctx, focus, next) -> do
      recordStep e ctx focus next
      case focus of
        Redex _ -> return next
        ROpCall op v -> throwError $ "unhandled operation call: " ++ show op ++ ", with argument: " ++ prettyShow v

eval :: (MonadError String m) => Expr Id -> m (Expr Id)
eval e = do
  stepRes <- evalStep e
  case stepRes of
    Nothing -> return e
    Just e' -> eval e'

evalWithSteps :: (MonadError String m, MonadWriter [Step Id] m) => Expr Id -> m (Expr Id)
evalWithSteps e = do
  stepRes <- evalStepWithSteps e
  case stepRes of
    Nothing -> return e
    Just e' -> evalWithSteps e'

evalWithFuel :: (MonadError String m) => Int -> Expr Id -> m (Maybe (Expr Id))
evalWithFuel fuel e
  | fuel <= 0 = do
      -- Fuel exhaustion is only reported when another reduction step exists.
      decomposeRes <- decomposeWith evalDecomposeCtx e
      case decomposeRes of
        Nothing -> return (Just e)
        Just _ -> return Nothing
  | otherwise = do
      stepRes <- evalStep e
      case stepRes of
        Nothing -> return (Just e)
        Just e' -> evalWithFuel (fuel - 1) e'

evalWithStepsFuel :: (MonadError String m, MonadWriter [Step Id] m) => Int -> Expr Id -> m (Maybe (Expr Id))
evalWithStepsFuel fuel e
  | fuel <= 0 = do
      -- Fuel exhaustion is only reported when another reduction step exists.
      decomposeRes <- decomposeWith evalDecomposeCtx e
      case decomposeRes of
        Nothing -> return (Just e)
        Just _ -> return Nothing
  | otherwise = do
      stepRes <- evalStepWithSteps e
      case stepRes of
        Nothing -> return (Just e)
        Just e' -> evalWithStepsFuel (fuel - 1) e'

eval'' :: (MonadError String m, MonadIO m) => Expr Id -> m (Expr Id)
eval'' e = do
  stepRes <- evalStep e
  case stepRes of
    Nothing -> return e
    Just e' -> do
      liftIO $ putStrLn $ "eval step: " ++ prettyShow e ++ " --> " ++ prettyShow e'
      eval'' e'

eval' :: Expr Id -> IO ()
eval' e = do
  evalRes <- runExceptT (eval'' e)
  case evalRes of
    Left err -> putStrLn $ "evaluation error: " ++ err
    Right v -> putStrLn $ "evaluation result: " ++ prettyShow v

runEval :: Expr Id -> Either String (Expr Id)
runEval e = runExcept (eval e)

runEvalWithSteps :: Expr Id -> Either String (Expr Id, [Step Id])
runEvalWithSteps e = runExcept (runWriterT (evalWithSteps e))

runEvalWithFuel :: Int -> Expr Id -> Either String (Maybe (Expr Id))
runEvalWithFuel fuel e = runExcept (evalWithFuel fuel e)

-- return Left (err, status)
runEvalWithStepsFuel :: Int -> Expr Id -> (Either (String, Int) (Expr Id), [Step Id])
runEvalWithStepsFuel fuel e =
  case runWriter (runExceptT (evalWithStepsFuel fuel e)) of
    (Left err, steps) -> (Left (err, 2), steps)
    (Right Nothing, steps) -> (Left ("Fuel exhausted", 3), steps)
    (Right (Just e'), steps) -> (Right e', steps)

data FocusPos = FocusPos
  { posLine :: Int,
    posColumn :: Int,
    posOffset :: Int
  }
  deriving (Show, Eq)

data FocusRange = FocusRange
  { rangeStart :: FocusPos,
    rangeEnd :: FocusPos
  }
  deriving (Show, Eq)

data FocusMark = FocusMark deriving (Show, Eq)

data RenderState = RenderState
  { rsBuilder :: ShowS,
    rsLine :: Int,
    rsColumn :: Int,
    rsOffset :: Int,
    rsStart :: Maybe FocusPos,
    rsEnd :: Maybe FocusPos,
    rsActive :: Bool
  }

prettyPrintExprWithInDo :: Bool -> Expr Id -> Doc ann
prettyPrintExprWithInDo inDoFlag e =
  let st = PrettyState {names = freshnames, inDo = inDoFlag, prec = 0}
   in runReader (prettyPrintPrec e) st

prettyPrintCtxWithFocus :: Bool -> ECtx Id -> Expr Id -> Doc FocusMark
prettyPrintCtxWithFocus inDoFlag ctx focusE =
  let st = PrettyState {names = freshnames, inDo = inDoFlag, prec = 0}
   in runReader (go ctx) st
  where
    withState :: Int -> Bool -> Reader PrettyState a -> Reader PrettyState a
    withState p inDoValue = local (\s -> s {prec = p, inDo = inDoValue})

    renderExprAt :: Int -> Bool -> Expr Id -> Reader PrettyState (Doc FocusMark)
    renderExprAt p inDoValue e = withState p inDoValue (prettyPrintPrec e)

    renderCtxAt :: Int -> Bool -> ECtx Id -> Reader PrettyState (Doc FocusMark)
    renderCtxAt p inDoValue ctx' = withState p inDoValue (go ctx')

    renderExprHere :: Bool -> Expr Id -> Reader PrettyState (Doc FocusMark)
    renderExprHere inDoValue e = local (\s -> s {inDo = inDoValue}) (prettyPrintPrec e)

    renderCtxHere :: Bool -> ECtx Id -> Reader PrettyState (Doc FocusMark)
    renderCtxHere inDoValue ctx' = local (\s -> s {inDo = inDoValue}) (go ctx')

    wrapAtCurrentPrec :: Int -> Doc FocusMark -> Reader PrettyState (Doc FocusMark)
    wrapAtCurrentPrec selfPrec doc = do
      ctxPrec <- asks prec
      return $ if needsParens selfPrec ctxPrec then parens doc else doc

    renderBinaryNode :: Int -> Reader PrettyState (Doc FocusMark) -> Reader PrettyState (Doc FocusMark) -> (Doc FocusMark -> Doc FocusMark -> Doc FocusMark) -> Reader PrettyState (Doc FocusMark)
    renderBinaryNode selfPrec leftM rightM mk = do
      l <- leftM
      r <- rightM
      wrapAtCurrentPrec selfPrec (mk l r)

    renderIfNode :: Int -> Reader PrettyState (Doc FocusMark) -> Reader PrettyState (Doc FocusMark) -> Reader PrettyState (Doc FocusMark) -> Reader PrettyState (Doc FocusMark)
    renderIfNode selfPrec condM thenM elseM = do
      c <- condM
      t <- thenM
      e <- elseM
      wrapAtCurrentPrec selfPrec (renderIfDoc c t e)

    go :: ECtx Id -> Reader PrettyState (Doc FocusMark)
    go H = do
      d <- prettyPrintPrec focusE
      return $ annotate FocusMark d
    go (BiOpL op ctx' e2) = do
      let (p, leftCtx, rightCtx) = biOpPrecContexts op
      renderBinaryNode p (renderCtxAt leftCtx False ctx') (renderExprAt rightCtx False e2) (renderBiOpDoc op)
    go (BiOpR op e1 ctx') = do
      let (p, leftCtx, rightCtx) = biOpPrecContexts op
      renderBinaryNode p (renderExprAt leftCtx False e1) (renderCtxAt rightCtx False ctx') (renderBiOpDoc op)
    go (ConsL ctx' e2) = do
      let (p, leftCtx, rightCtx) = consPrecContexts
      renderBinaryNode p (renderCtxAt leftCtx False ctx') (renderExprAt rightCtx False e2) renderConsDoc
    go (ConsR e1 ctx') = do
      let (p, leftCtx, rightCtx) = consPrecContexts
      renderBinaryNode p (renderExprAt leftCtx False e1) (renderCtxAt rightCtx False ctx') renderConsDoc
    go (UnConsP ctx' e2 x k scope) = do
      let consExpr = instantiate2 (Var x) (Var k) scope
      e1' <- renderCtxHere False ctx'
      nilDoc <- renderExprHere False e2
      consDoc <- renderExprHere False consExpr
      return $ renderUnConsDoc x k e1' nilDoc consDoc
    go (PairL ctx' e2) = do
      l <- renderCtxHere False ctx'
      r <- renderExprHere False e2
      return $ renderPairDoc l r
    go (PairR e1 ctx') = do
      l <- renderExprHere False e1
      r <- renderCtxHere False ctx'
      return $ renderPairDoc l r
    go (InLorRI b ctx') = do
      e' <- renderCtxHere False ctx'
      return $ renderInLorRDoc b e'
    go (UnEitherP ctx' x le y re) = do
      let le' = instantiate1 (Var x) le
          re' = instantiate1 (Var y) re
      e' <- renderCtxHere False ctx'
      le'' <- renderExprHere False le'
      re'' <- renderExprHere False re'
      return $ renderUnEitherDoc x y e' le'' re''
    go (AppL ctx' e2) = do
      let (p, leftCtx, rightCtx) = appPrecContexts
      renderBinaryNode p (renderCtxAt leftCtx False ctx') (renderExprAt rightCtx False e2) renderAppDoc
    go (AppR e1 ctx') = do
      let (p, leftCtx, rightCtx) = appPrecContexts
      renderBinaryNode p (renderExprAt leftCtx False e1) (renderCtxAt rightCtx False ctx') renderAppDoc
    go (IfC ctx' e2 e3) = do
      let (p, childCtx) = ifPrecContexts
      renderIfNode p (renderCtxAt childCtx False ctx') (renderExprAt childCtx False e2) (renderExprAt childCtx False e3)
    go (UnPairP ctx' a b scope) = do
      e' <- renderCtxHere False ctx'
      e2' <- renderExprHere False (instantiate2 (Var a) (Var b) scope)
      return $ renderUnpairDoc a b e' e2'
    go (OpCallE op ctx') = do
      e' <- renderCtxHere False ctx'
      return $ renderOpCallDoc op e'
    go (WithH ctx' e2) = do
      e1' <- renderCtxHere False ctx'
      e2' <- renderExprHere False e2
      return $ renderWithDoc e1' e2'
    go (WithB e1 ctx') = do
      e1' <- renderExprHere False e1
      e2' <- renderCtxHere False ctx'
      return $ renderWithDoc e1' e2'
    go (Do1 ctx' x scope) = do
      inDoCtx <- asks inDo
      rhsDoc <- renderCtxHere False ctx'
      let bodyExpr = instantiate1 (Var x) scope
      bodyDoc <- case bodyExpr of
        Do {} -> renderExprHere True bodyExpr
        LetRec {} -> renderExprHere True bodyExpr
        _ -> renderExprHere False bodyExpr
      return $ renderDoDoc inDoCtx x rhsDoc bodyDoc

renderWithFocusRange :: LayoutOptions -> Doc FocusMark -> (String, Maybe FocusRange)
renderWithFocusRange l doc =
  let finalState = execState (consume (layoutPretty l doc)) initialRenderState
      text = rsBuilder finalState ""
   in (text, FocusRange <$> rsStart finalState <*> rsEnd finalState)
  where
    initialRenderState :: RenderState
    initialRenderState =
      RenderState
        { rsBuilder = id,
          rsLine = 1,
          rsColumn = 1,
          rsOffset = 0,
          rsStart = Nothing,
          rsEnd = Nothing,
          rsActive = False
        }

    currentPos :: State RenderState FocusPos
    currentPos = do
      l <- gets rsLine
      c <- gets rsColumn
      o <- gets rsOffset
      pure (FocusPos l c o)

    appendText :: String -> State RenderState ()
    appendText str = do
      modify' $ \st -> st {rsBuilder = rsBuilder st . (str ++)}
      mapM_ advanceChar str

    advanceChar :: Char -> State RenderState ()
    advanceChar ch =
      modify' $ \st ->
        if ch == '\n'
          then st {rsLine = rsLine st + 1, rsColumn = 1, rsOffset = rsOffset st + 1}
          else st {rsColumn = rsColumn st + 1, rsOffset = rsOffset st + 1}

    consume :: SimpleDocStream FocusMark -> State RenderState ()
    consume SFail = pure ()
    consume SEmpty = pure ()
    consume (SChar ch rest) = appendText [ch] >> consume rest
    consume (SText _ t rest) = appendText (T.unpack t) >> consume rest
    consume (SLine i rest) = appendText ('\n' : replicate i ' ') >> consume rest
    consume (SAnnPush FocusMark rest) = do
      st <- gets rsStart
      p <- currentPos
      modify' $ \s -> s {rsStart = st <|> Just p, rsActive = True}
      consume rest
    consume (SAnnPop rest) = do
      active <- gets rsActive
      p <- currentPos
      when active $ modify' $ \s -> s {rsEnd = Just p}
      modify' $ \s -> s {rsActive = False}
      consume rest

prettyShowContext' :: LayoutOptions -> ECtx Id -> String
prettyShowContext' l ctx =
  let doc = prettyPrintCtxWithFocus False ctx (ExprHole 999999999 Nothing [])
   in fst (renderWithFocusRange l doc)

prettyShowContext :: ECtx Id -> String
prettyShowContext = makeShow prettyShowContext'

prettyShowStepFocusedWithRange' :: LayoutOptions -> Step Id -> (String, Maybe FocusRange)
prettyShowStepFocusedWithRange' l step =
  let focusE = focusExpr (stepFocus step)
      renderedDoc = prettyPrintCtxWithFocus False (stepContext step) focusE
      (rendered, range) = renderWithFocusRange l renderedDoc
      expected = prettyShow' l (stepFocusedExpr step)
   in
    if rendered == expected
      then (rendered, range)
      else
        error
          ( "assertion failed: prettyShowWidthStepFocusedWithRange mismatch\n"
              ++ "rendered: "
              ++ rendered
              ++ "\nexpected: "
              ++ expected
              ++ "\ncontext: "
              ++ show (stepContext step)
              ++ "\nfocus: "
              ++ show (stepFocus step)
          )
prettyShowWidthStepFocusedWithRange :: Int -> Step Id -> (String, Maybe FocusRange)
prettyShowWidthStepFocusedWithRange = makeWidth prettyShowStepFocusedWithRange' 

prettyShowStepFocusedWithRange :: Step Id -> (String, Maybe FocusRange)
prettyShowStepFocusedWithRange = makeShow prettyShowStepFocusedWithRange' 
