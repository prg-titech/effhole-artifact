{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
module Internal.Norm (norm, normWithSteps) where

import Bound
import Bound.Scope
import Common
import Control.Monad (foldM)
import Control.Monad.Except
import Control.Monad.State (evalStateT)
import Control.Monad.State.Class
import Control.Monad.Writer (runWriter)
import Control.Monad.Writer.Class
import Data.Foldable (toList)
import qualified Data.Set as S
import External (BindVar(..))
import Internal.Eval hiding (reduce, isValue, isIndet, isFinal, isPureHole, isRetHandled, decompose', getRedexOp, guardWith)
import qualified Internal.Eval as E
import Internal.Syntax

renameHoleVar :: (Id, Id) -> Expr Id -> Expr Id
renameHoleVar (old, new) = go
  where
    go :: forall a. Expr a -> Expr a
    go = \case
      ExprHole i j subst -> 
        ExprHole i j [ if name x == old then (x {name = new}, ex) else (x, go ex) | (x, ex) <- subst ]

      Abs x scope
        | x == old -> Abs x scope
        | otherwise -> Abs x (hoistScope go scope)

      Handler h scope cases ->
        let scope' = if h == old then scope else hoistScope go scope
            cases' = [ (op, (x, k, if x == old || k == old then s else hoistScope go s)) 
                     | (op, (x, k, s)) <- cases ]
        in Handler h scope' cases'

      UnCons e1 e2 x k scope ->
        let scope' = if x == old || k == old then scope else hoistScope go scope
        in UnCons (go e1) (go e2) x k scope'

      UnEither e1 x le y re ->
        let le' = if x == old then le else hoistScope go le
            re' = if y == old then re else hoistScope go re
        in UnEither (go e1) x le' y re'

      Unpair e1 x y scope ->
        let scope' = if x == old || y == old then scope else hoistScope go scope
        in Unpair (go e1) x y scope'

      Do e1 x scope ->
        let scope' = if x == old then scope else hoistScope go scope
        in Do (go e1) x scope'
      
      LetRec f x s1 s2 ->
        let s2' = if f == old then s2 else hoistScope go s2
            s1' = if f == old || x == old then s1 else hoistScope go s1
        in LetRec f x s1' s2'

      App e1 e2 -> App (go e1) (go e2)
      BiOp op e1 e2 -> BiOp op (go e1) (go e2)
      Cons e1 e2 -> Cons (go e1) (go e2)
      Pair e1 e2 -> Pair (go e1) (go e2)
      InLorR b e -> InLorR b (go e)
      If e1 e2 e3 -> If (go e1) (go e2) (go e3)
      With e1 e2 -> With (go e1) (go e2)
      OpCall op e1 -> OpCall op (go e1)

      e -> e

isValue :: Expr a -> Bool
isValue (Var _) = True
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

isIndet :: Expr a -> Bool
isIndet (BiOp _ e1 e2) = isIndet e1 || isIndet e2
isIndet (Cons e1 e2) = isIndet e1 || isIndet e2
isIndet (UnCons Cons {} _ _ _ _) = False
isIndet (UnCons l _ _ _ _) = isIndet l
isIndet (Pair e1 e2) = isIndet e1 || isIndet e2
isIndet (InLorR _ e) = isIndet e
isIndet (UnEither e _ _ _ _) = isIndet e
isIndet ExprHole {} = True
isIndet (App f _) = isIndet f
isIndet (If b _ _) = isIndet b
isIndet (Unpair Pair {} _ _ _) = False
isIndet (Unpair p _ _ _) = isIndet p
isIndet (With h _) = isIndet h
isIndet _ = False

isPureHole :: Expr a -> Bool
isPureHole ExprHole{} = True
isPureHole _ = False

isRetHandled :: Expr a -> Bool
isRetHandled x = isValue x || isPureHole x

isFinal :: Expr a -> Bool
isFinal e = isValue e || isIndet e

normDecomposeCtx :: DecomposeCtx
normDecomposeCtx = DecomposeCtx isValue isFinal isRetHandled

-- | Normalize an expression by repeatedly applying reduction strategy
-- and descending into binders.
-- It reuses 'reduce' from "Internal.Eval" effectively.
norm :: Int -> Expr Id -> Maybe (Expr Id)
norm fuel e = either (const Nothing) Just (fst $ normWithSteps fuel e)

normWithSteps :: Int -> Expr Id -> (Either (String, Int) (Expr Id), [Step Id])
normWithSteps fuel e =
  case runWriter (runExceptT (evalStateT (normM e) fuel)) of
    (Left _, b) -> (Left ("Fuel exhausted", 3), b)
    (Right e', b) -> (Right e', b)

-- | open the scope, renaming the bound variable, 
-- updating the body and any occurrences in ExprHole substitutions
renameScope1 :: (Id, Id) -> Scope () Expr Id -> Expr Id
renameScope1 (old, new) scope = renameHoleVar (old, new) $ instantiate1 (Var new) scope

renameScope2 :: (Id, Id) -> (Id, Id) -> Scope XOrK Expr Id -> Expr Id
renameScope2 (oldX, newX) (oldK, newK) scope =
  renameHoleVar (oldX, newX) $ renameHoleVar (oldK, newK) $ instantiate2 (Var newX) (Var newK) scope

-- | Descend into sub-expressions, normalizing them.
-- Handles binders by instantiating with fresh variables.
descendM :: (MonadError String m, MonadState Int m, MonadWriter [Step Id] m) => Expr Id -> m (Expr Id)
descendM e = case e of
  Abs x scope ->
    let used = S.fromList (toList scope)
        x' = fresh used x
        body = renameScope1 (x, x') scope
     in do
       body' <-
         liftSteps
           (\bodyStep -> Abs x' (abstract1 x' bodyStep))
           id
           (normM body)
       return $ Abs x' (abstract1 x' body')
     
  Handler h scope cases ->
    let usedScope = S.fromList (toList scope)
        h' = fresh usedScope h
        scopeBody = renameScope1 (h, h') scope
        
        normCase scopeNow (op, (x, k, s)) =
           let usedS = S.fromList (toList s)
               -- We need to choose x' and k' fresh relative to s
               x' = fresh usedS x
               k' = fresh (S.insert x' usedS) k
               sBody = renameScope2 (x, x') (k, k') s
           in do
             sBody' <-
               liftSteps
                 (\bodyStep -> Handler h' (abstract1 h' scopeNow) [(op, (x', k', abstract2 x' k' bodyStep))])
                 id
                 (normM sBody)
             return (op, (x', k', abstract2 x' k' sBody'))
     in do
       normScope <-
         liftSteps
           (\scopeStep -> Handler h' (abstract1 h' scopeStep) cases)
           id
           (normM scopeBody)
       normCases <- foldM (\built c -> do
                      c' <- normCase normScope c
                      return (built ++ [c'])) [] cases
       return $ Handler h (abstract1 h' normScope) normCases

  App e1 e2 -> do
    e1' <- liftSteps (\s -> App s e2) (\ctx -> AppL ctx e2) (normM e1)
    e2' <- liftSteps (\s -> App e1' s) (\ctx -> AppR e1' ctx) (normM e2)
    return $ App e1' e2'

  BiOp op e1 e2 -> do
    e1' <- liftSteps (\s -> BiOp op s e2) (\ctx -> BiOpL op ctx e2) (normM e1)
    e2' <- liftSteps (\s -> BiOp op e1' s) (\ctx -> BiOpR op e1' ctx) (normM e2)
    return $ BiOp op e1' e2'

  Cons e1 e2 -> do
    e1' <- liftSteps (\s -> Cons s e2) (\ctx -> ConsL ctx e2) (normM e1)
    e2' <- liftSteps (\s -> Cons e1' s) (\ctx -> ConsR e1' ctx) (normM e2)
    return $ Cons e1' e2'
  
  UnCons e1 e2 x k scope ->
     let used = S.fromList (toList scope)
         x' = fresh used x
         k' = fresh (S.insert x' used) k
         body = renameScope2 (x, x') (k, k') scope
      in do
        e1' <-
          liftSteps
            (\s -> UnCons s e2 x' k' (abstract2 x' k' body))
            (\ctx -> UnConsP ctx e2 x' k' (abstract2 x' k' body))
            (normM e1)
        e2' <-
          liftSteps
            (\s -> UnCons e1' s x' k' (abstract2 x' k' body))
            id
            (normM e2)
        body' <-
          liftSteps
            (\s -> UnCons e1' e2' x' k' (abstract2 x' k' s))
            id
            (normM body)
        return $ UnCons e1' e2' x' k' (abstract2 x' k' body')

  Pair e1 e2 -> do
    e1' <- liftSteps (\s -> Pair s e2) (\ctx -> PairL ctx e2) (normM e1)
    e2' <- liftSteps (\s -> Pair e1' s) (\ctx -> PairR e1' ctx) (normM e2)
    return $ Pair e1' e2'

  InLorR b e1 -> do
    e1' <- liftSteps (\s -> InLorR b s) (\ctx -> InLorRI b ctx) (normM e1)
    return $ InLorR b e1'
  
  UnEither e1 x le y re ->
     let usedL = S.fromList (toList le)
         x' = fresh usedL x
         leBody = renameScope1 (x, x') le
         
         usedR = S.fromList (toList re)
         y' = fresh usedR y
         reBody = renameScope1 (y, y') re
     in do
       e1' <-
         liftSteps
           (\s -> UnEither s x' (abstract1 x' leBody) y' (abstract1 y' reBody))
           (\ctx -> UnEitherP ctx x' (abstract1 x' leBody) y' (abstract1 y' reBody))
           (normM e1)
       le' <-
         liftSteps
           (\s -> UnEither e1' x' (abstract1 x' s) y' (abstract1 y' reBody))
           id
           (normM leBody)
       re' <-
         liftSteps
           (\s -> UnEither e1' x' (abstract1 x' le') y' (abstract1 y' s))
           id
           (normM reBody)
       return $ UnEither e1' x' (abstract1 x' le') y' (abstract1 y' re')

  If e1 e2 e3 -> do
    e1' <- liftSteps (\s -> If s e2 e3) (\ctx -> IfC ctx e2 e3) (normM e1)
    e2' <- liftSteps (\s -> If e1' s e3) id (normM e2)
    e3' <- liftSteps (\s -> If e1' e2' s) id (normM e3)
    return $ If e1' e2' e3'
  
  Unpair e1 x y scope ->
     let used = S.fromList (toList scope)
         x' = fresh used x
         y' = fresh (S.insert x' used) y
         body = renameScope2 (x, x') (y, y') scope
      in do
        e1' <-
          liftSteps
            (\s -> Unpair s x' y' (abstract2 x' y' body))
            (\ctx -> UnPairP ctx x' y' (abstract2 x' y' body))
            (normM e1)
        body' <-
          liftSteps
            (\s -> Unpair e1' x' y' (abstract2 x' y' s))
            id
            (normM body)
        return $ Unpair e1' x' y' (abstract2 x' y' body')

  With e1 e2 -> do
    e1' <- liftSteps (\s -> With s e2) (\ctx -> WithH ctx e2) (normM e1)
    e2' <- liftSteps (\s -> With e1' s) (\ctx -> WithB e1' ctx) (normM e2)
    return $ With e1' e2'
  
  Do e1 x scope ->
     let used = S.fromList (toList scope)
         x' = fresh used x
         body = renameScope1 (x, x') scope
      in do
        e1' <-
          liftSteps
            (\s -> Do s x' (abstract1 x' body))
            (\ctx -> Do1 ctx x' (abstract1 x' body))
            (normM e1)
        body' <-
          liftSteps
            (\s -> Do e1' x' (abstract1 x' s))
            id
            (normM body)
        return $ Do e1' x' (abstract1 x' body')
      
  -- Normalize substitutions atomically: keep their normalized result,
  -- but do not expose inner reduction steps in the outer trace.
  ExprHole i j subst -> do
    fuel0 <- get
    let subst' = map (\(x, ex) -> case norm (min fuel0 10) ex of
         Nothing -> (x, ex)
         Just ex' -> (x, ex')) subst
    return $ ExprHole i j subst'
  OpCall op e1 -> do
    e1' <- liftSteps (\s -> OpCall op s) (\ctx -> OpCallE op ctx) (normM e1)
    return $ OpCall op e1'
  
  -- LetRec f x s1 s2 ->
  --    let used1 = S.fromList (toList s1)
  --        f' = fresh used1 f
  --        x' = fresh (S.insert f' used1) x
  --        -- s1 binds f (X) and x (K) in order of abstract2 f x
  --        body1 = renameScope2 (f, f') (x, x') s1
         
  --        used2 = S.fromList (toList s2)
  --        f'' = fresh used2 f
  --        body2 = renameScope1 (f, f'') s2
  --    in LetRec f' x' (abstract2 f' x' (norm body1)) (abstract1 f'' (norm body2))

  -- Leaf nodes
  _ -> return e

consumeFuel :: (MonadError String m, MonadState Int m) => m ()
consumeFuel = do
  fuel <- get
  if fuel <= 0
    then throwError "Normalization fuel exhausted"
    else put (fuel - 1)

normM :: (MonadError String m, MonadState Int m, MonadWriter [Step Id] m) => Expr Id -> m (Expr Id)
normM e = do
  decomposeRes <- catchError (Right <$> E.decomposeReduceWith normDecomposeCtx e) (return . Left)
  case decomposeRes of
    Right (Just (ctx, focus@(Redex _), Just next)) -> do
      consumeFuel
      E.recordStep e ctx focus (Just next)
      normM next
    _ -> descendM e

-- | Generate a fresh name avoiding the used set, based on a hint.
fresh :: S.Set Id -> Id -> Id
fresh used x = if x `S.member` used then fresh used (x <> "'") else x

liftSteps
  :: (MonadWriter [Step Id] m)
  => (Expr Id -> Expr Id)
  -> (ECtx Id -> ECtx Id)
  -> m a
  -> m a
liftSteps wrapExpr wrapCtx action = do
  (res, steps) <- censor (const []) (listen action)
  tell
    [ Step
        { stepBefore = wrapExpr (stepBefore st),
          stepContext = wrapCtx (stepContext st),
          stepFocus = stepFocus st,
          stepAfter = fmap wrapExpr (stepAfter st)
        }
      | st <- steps
    ]
  return res

