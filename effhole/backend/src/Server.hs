{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Server where

import Bound
import Internal
import qualified External as E
import External (BindVar(..))
import Parser
import Elaboration
import Common
import qualified Data.Map as M
import qualified Data.Text as T

import Data.Aeson ( FromJSON(..), (.=), (.:), (.:?), object, withObject )
import Data.Aeson.Key as K
import qualified Data.Aeson.KeyMap as KM
import qualified Data.ByteString.Lazy.Char8 as BSL
import qualified Data.ByteString.Char8 as BS
import qualified Data.Aeson as A
import Data.Aeson.Types (parseMaybe, Pair)
import GHC.Generics (Generic)
import Network.HTTP.Types (Status, status200, status400, status404, status405, status422)
import Network.HTTP.Types.Header (hContentType)
import Network.Wai (Application, requestMethod, rawPathInfo, responseLBS, strictRequestBody)
import Network.Wai.Handler.Warp (run)

import Control.Exception (SomeException, catch)
import Control.Monad.State
import System.IO (hPutStrLn, stderr)

resultWidth, contextWidth :: Int
resultWidth = 70
contextWidth = 55

type HoleIdState = (M.Map Int Int, M.Map String A.Value)
type Subst a = [(BindVar, Expr a)]
type HoleRenumberState = (Int, M.Map Int Int)

data BoundFrame = Frame1 Id | Frame2 Id Id

type BoundEnv = [BoundFrame]

emptyBoundEnv :: BoundEnv
emptyBoundEnv = []

pushBoundFrame :: BoundFrame -> BoundEnv -> BoundEnv
pushBoundFrame = (:) 

popBoundFrame :: BoundEnv -> BoundEnv
popBoundFrame (_ : frames) = frames
popBoundFrame env = env

class BoundIndex b where
  lookupBound :: BoundFrame -> b -> Id

instance BoundIndex () where
  lookupBound (Frame1 x) () = x
  lookupBound (Frame2 _ _) () = "Internal error, please report it as a bug."

instance BoundIndex XOrK where
  lookupBound (Frame2 x _) X = x
  lookupBound (Frame2 _ k) K = k
  lookupBound (Frame1 _) _ = "Internal error, please report it as a bug."

lookupBoundEnv :: BoundIndex b => BoundEnv -> b -> Id
lookupBoundEnv (frame : _) b = lookupBound frame b
lookupBoundEnv _ _ = "Internal error, please report it as a bug."

class ReifyId a where
  reifyId :: BoundEnv -> a -> Id

instance ReifyId Id where
  reifyId _ = id

instance (BoundIndex b, ReifyId a) => ReifyId (Var b a) where
  reifyId env (B b) = lookupBoundEnv env b
  reifyId env (F a) = reifyId (popBoundFrame env) a

reifyExpr :: ReifyId a => BoundEnv -> Expr a -> Expr Id
reifyExpr env expr = case expr of
  Var a -> Var (reifyId env a)
  BV b -> BV b
  NV n -> NV n
  Str s -> Str s
  Unit -> Unit
  BiOp op e1 e2 -> BiOp op (reifyExpr env e1) (reifyExpr env e2)
  Nil -> Nil
  Cons e1 e2 -> Cons (reifyExpr env e1) (reifyExpr env e2)
  UnCons e1 e2 x k scope ->
    let env' = pushBoundFrame (Frame2 x k) env
        body' = reifyExpr env' (fromScope scope)
     in UnCons (reifyExpr env e1) (reifyExpr env e2) x k (abstract2 x k body')
  Abs x scope ->
    let env' = pushBoundFrame (Frame1 x) env
        body' = reifyExpr env' (fromScope scope)
     in Abs x (abstract1 x body')
  Pair e1 e2 -> Pair (reifyExpr env e1) (reifyExpr env e2)
  InLorR b e -> InLorR b (reifyExpr env e)
  UnEither e x le y re ->
    let envL = pushBoundFrame (Frame1 x) env
        envR = pushBoundFrame (Frame1 y) env
        le' = reifyExpr envL (fromScope le)
        re' = reifyExpr envR (fromScope re)
     in UnEither (reifyExpr env e) x (abstract1 x le') y (abstract1 y re')
  Handler x scope cases ->
    let env' = pushBoundFrame (Frame1 x) env
        body' = reifyExpr env' (fromScope scope)
        cases' = map
          (\(op, (a, k, s)) ->
             let envC = pushBoundFrame (Frame2 a k) env
                 bodyC = reifyExpr envC (fromScope s)
              in (op, (a, k, abstract2 a k bodyC)))
          cases
     in Handler x (abstract1 x body') cases'
  ExprHole i j subst -> ExprHole i j [ (x, reifyExpr env e) | (x, e) <- subst ]
  App e1 e2 -> App (reifyExpr env e1) (reifyExpr env e2)
  If e1 e2 e3 -> If (reifyExpr env e1) (reifyExpr env e2) (reifyExpr env e3)
  Unpair e a b scope ->
    let env' = pushBoundFrame (Frame2 a b) env
        body' = reifyExpr env' (fromScope scope)
     in Unpair (reifyExpr env e) a b (abstract2 a b body')
  OpCall op e -> OpCall op (reifyExpr env e)
  With e1 e2 -> With (reifyExpr env e1) (reifyExpr env e2)
  Do e x scope ->
    let env' = pushBoundFrame (Frame1 x) env
        body' = reifyExpr env' (fromScope scope)
     in Do (reifyExpr env e) x (abstract1 x body')
  LetRec f x s1 s2 ->
    let envS1 = pushBoundFrame (Frame2 f x) env
        envS2 = pushBoundFrame (Frame1 f) env
        s1' = reifyExpr envS1 (fromScope s1)
        s2' = reifyExpr envS2 (fromScope s2)
     in LetRec f x (abstract2 f x s1') (abstract1 f s2')

freshHoleId :: Int -> State HoleRenumberState Int
freshHoleId oldId = do
  (nextId, oldToNew) <- get
  case M.lookup oldId oldToNew of
    Just newId -> return newId
    Nothing -> do
      put (nextId + 1, M.insert oldId nextId oldToNew)
      return nextId

normalizeExternalExpr :: E.Expr -> State HoleRenumberState E.Expr
normalizeExternalExpr (E.Var x) = return $ E.Var x
normalizeExternalExpr (E.BV b) = return $ E.BV b
normalizeExternalExpr (E.NV n) = return $ E.NV n
normalizeExternalExpr (E.Str s) = return $ E.Str s
normalizeExternalExpr E.Unit = return E.Unit
normalizeExternalExpr (E.BiOp op e1 e2) = do
  e1' <- normalizeExternalExpr e1
  e2' <- normalizeExternalExpr e2
  return $ E.BiOp op e1' e2'
normalizeExternalExpr E.Nil = return E.Nil
normalizeExternalExpr (E.Cons e1 e2) = do
  e1' <- normalizeExternalExpr e1
  e2' <- normalizeExternalExpr e2
  return $ E.Cons e1' e2'
normalizeExternalExpr (E.UnCons e1 e2 x k e3) = do
  e1' <- normalizeExternalExpr e1
  e2' <- normalizeExternalExpr e2
  e3' <- normalizeExternalExpr e3
  return $ E.UnCons e1' e2' x k e3'
normalizeExternalExpr (E.Abs x xs e) = do
  e' <- normalizeExternalExpr e
  return $ E.Abs x xs e'
normalizeExternalExpr (E.Pair e1 e2) = do
  e1' <- normalizeExternalExpr e1
  e2' <- normalizeExternalExpr e2
  return $ E.Pair e1' e2'
normalizeExternalExpr (E.InLorR b e) = do
  e' <- normalizeExternalExpr e
  return $ E.InLorR b e'
normalizeExternalExpr (E.UnEither e x le y re) = do
  e' <- normalizeExternalExpr e
  le' <- normalizeExternalExpr le
  re' <- normalizeExternalExpr re
  return $ E.UnEither e' x le' y re'
normalizeExternalExpr (E.Handler handlerName e cases) = do
  e' <- normalizeExternalExpr e
  cases' <- mapM normalizeHandlerCase cases
  return $ E.Handler handlerName e' cases'
  where
    normalizeHandlerCase (E.HandlerCase op caseName k caseExpr) = do
      caseExpr' <- normalizeExternalExpr caseExpr
      return $ E.HandlerCase op caseName k caseExpr'
normalizeExternalExpr (E.ExprHole oldId) = E.ExprHole <$> freshHoleId oldId
normalizeExternalExpr (E.App e1 e2) = do
  e1' <- normalizeExternalExpr e1
  e2' <- normalizeExternalExpr e2
  return $ E.App e1' e2'
normalizeExternalExpr (E.If e1 e2 e3) = do
  e1' <- normalizeExternalExpr e1
  e2' <- normalizeExternalExpr e2
  e3' <- normalizeExternalExpr e3
  return $ E.If e1' e2' e3'
normalizeExternalExpr (E.Unpair e x y e2) = do
  e' <- normalizeExternalExpr e
  e2' <- normalizeExternalExpr e2
  return $ E.Unpair e' x y e2'
normalizeExternalExpr (E.OpCall op e) = do
  e' <- normalizeExternalExpr e
  return $ E.OpCall op e'
normalizeExternalExpr (E.With e1 e2) = do
  e1' <- normalizeExternalExpr e1
  e2' <- normalizeExternalExpr e2
  return $ E.With e1' e2'
normalizeExternalExpr (E.Do stmts e) = do
  stmts' <- mapM normalizeDoStmt stmts
  e' <- normalizeExternalExpr e
  return $ E.Do stmts' e'
  where
    normalizeDoStmt (E.DoBind x stmtExpr) = E.DoBind x <$> normalizeExternalExpr stmtExpr
    normalizeDoStmt (E.DoExpr stmtExpr) = E.DoExpr <$> normalizeExternalExpr stmtExpr
    normalizeDoStmt (E.LetRec f x xs stmtExpr) = E.LetRec f x xs <$> normalizeExternalExpr stmtExpr

normalizeHoleMap :: M.Map Int Int -> M.Map CodePos Int -> M.Map CodePos String
normalizeHoleMap oldToNew = M.fromList . map remap . M.toList
  where
    remap (pos, oldId) = (pos, show (oldToNew M.! oldId))

normalizeParsedProgram :: (E.Expr, M.Map CodePos Int) -> (E.Expr, M.Map CodePos String)
normalizeParsedProgram (expr, holeMap) =
  let (expr', (_, oldToNew)) = runState (normalizeExternalExpr expr) (1, M.empty)
   in (expr', normalizeHoleMap oldToNew holeMap)

getId :: Int -> State HoleIdState Int
getId i = do
  (m1, m2) <- get
  case M.lookup i m1 of
    Just j -> put (M.insert i (j+1) m1, m2) >> return j
    Nothing -> put (M.insert i 2 m1, m2) >> return 1

updateSubstMap :: String -> Subst Id -> State HoleIdState ()
updateSubstMap holeName subst = do
  (m1, m2) <- get
  put (m1, M.insert holeName (showSubst subst) m2)
  where
    showSubst :: Subst Id -> A.Value
    showSubst = A.Object . KM.fromList . map showEntry

    showEntry :: (BindVar, Expr Id) -> Pair
    showEntry (x, v) =
      K.fromText (name x) .= object
        [ "value" .= prettyShowWidth contextWidth v
        , "definition" .= object
            [ "start" .= posToJSON (startPos x)
            , "end" .= posToJSON (endPos x)
            ]
        ]

    posToJSON :: CodePos -> A.Value
    posToJSON (line, column) = object
      [ "line" .= line
      , "column" .= column
      ]

hoistScopeWith :: forall b v. (BoundIndex b, ReifyId v) => BoundEnv -> BoundFrame -> Scope b Expr v -> State HoleIdState (Scope b Expr v)
hoistScopeWith env frame scope = do
  body' <- assignHoleIdVWith (pushBoundFrame frame env) (fromScope scope)
  return $ toScope body'

assignHoleIdVWith :: ReifyId a => BoundEnv -> Expr a -> State HoleIdState (Expr a)
assignHoleIdVWith _ (Var v) = return $ Var v
assignHoleIdVWith _ (NV n) = return $ NV n
assignHoleIdVWith _ (BV b) = return $ BV b
assignHoleIdVWith _ (Str s) = return $ Str s
assignHoleIdVWith _ Unit = return Unit
assignHoleIdVWith _ Nil = return Nil
assignHoleIdVWith env (BiOp op v1 v2) = do
  v1' <- assignHoleIdVWith env v1
  v2' <- assignHoleIdVWith env v2
  return $ BiOp op v1' v2'
assignHoleIdVWith env (Cons v1 v2) = do
  v1' <- assignHoleIdVWith env v1
  v2' <- assignHoleIdVWith env v2
  return $ Cons v1' v2'
assignHoleIdVWith env (UnCons v1 v2 id1 id2 s) = do
  v1' <- assignHoleIdVWith env v1
  v2' <- assignHoleIdVWith env v2
  s' <- hoistScopeWith env (Frame2 id1 id2) s
  return $ UnCons v1' v2' id1 id2 s'
assignHoleIdVWith env (Abs x s) = do
  s' <- hoistScopeWith env (Frame1 x) s
  return $ Abs x s'
assignHoleIdVWith env (Pair v1 v2) = do
  v1' <- assignHoleIdVWith env v1
  v2' <- assignHoleIdVWith env v2
  return $ Pair v1' v2'
assignHoleIdVWith env (InLorR b v) = do
  v' <- assignHoleIdVWith env v
  return $ InLorR b v'
assignHoleIdVWith env (UnEither e x le y re) = do
  e' <- assignHoleIdVWith env e
  le' <- hoistScopeWith env (Frame1 x) le
  re' <- hoistScopeWith env (Frame1 y) re
  return $ UnEither e' x le' y re'
assignHoleIdVWith env (Handler x cr hcs) = do
  cr' <- hoistScopeWith env (Frame1 x) cr
  hcs' <- mapM f hcs
  return $ Handler x cr' hcs'
  where
    f (op, (a, k, s)) = do
      s' <- hoistScopeWith env (Frame2 a k) s
      return (op, (a, k, s'))
assignHoleIdVWith env (ExprHole i _ s) = do
  j <- getId i
  s' <- assignHoleIdS env s
  let s_log = map (\(k, v) -> (k, reifyExpr env v)) s'
  updateSubstMap (show i ++ "_" ++ show j) s_log
  return $ ExprHole i (Just j) s'
assignHoleIdVWith env (App v1 v2) = do
  v1' <- assignHoleIdVWith env v1
  v2' <- assignHoleIdVWith env v2
  return $ App v1' v2'
assignHoleIdVWith env (If v c1 c2) = do
  v' <- assignHoleIdVWith env v
  c1' <- assignHoleIdVWith env c1
  c2' <- assignHoleIdVWith env c2
  return $ If v' c1' c2'
assignHoleIdVWith env (Unpair v a b s) = do
  v' <- assignHoleIdVWith env v
  s' <- hoistScopeWith env (Frame2 a b) s
  return $ Unpair v' a b s'
assignHoleIdVWith env (OpCall op v) = do
  v' <- assignHoleIdVWith env v
  return $ OpCall op v'
assignHoleIdVWith env (With v c) = do
  v' <- assignHoleIdVWith env v
  c' <- assignHoleIdVWith env c
  return $ With v' c'
assignHoleIdVWith env (Do c x s) = do
  c1' <- assignHoleIdVWith env c
  s' <- hoistScopeWith env (Frame1 x) s
  return $ Do c1' x s'
assignHoleIdVWith env (LetRec f x s1 s2) = do
  s1' <- hoistScopeWith env (Frame2 f x) s1
  s2' <- hoistScopeWith env (Frame1 f) s2
  return $ LetRec f x s1' s2'

assignHoleIdV :: ReifyId a => Expr a -> State HoleIdState (Expr a)
assignHoleIdV = assignHoleIdVWith emptyBoundEnv

assignHoleIdS :: ReifyId a => BoundEnv -> [(BindVar, Expr a)] -> State HoleIdState [(BindVar, Expr a)]
assignHoleIdS env subst = do
  mapM f subst
  where
    f (x, v) = do
      v' <- assignHoleIdVWith env v
      return (x, v')

assignHoleIds :: Expr Id -> (Expr Id, HoleIdState)
assignHoleIds c = runState (assignHoleIdV c) (M.empty, M.empty)


assignHoleResToJSON :: (Expr Id, HoleIdState) -> [Pair]
assignHoleResToJSON (c, (m1, m2)) = 
         [ "result" .= prettyShowWidth resultWidth c
         , "holeIds" .= map f (M.toList m1)
         , "substMap" .= A.toJSON m2
         ] 
  where
    f (k, v) = object [ "holeId" .= k, "count" .= v ]

successStatus :: [Pair]
successStatus = [ "status" .= (0 :: Int) ]

stepToJSON :: Int -> Step Id -> A.Value
stepToJSON i step =
  let before = object . assignHoleResToJSON . assignHoleIds $ stepBefore step
      (_, focusedRange) = prettyShowWidthStepFocusedWithRange resultWidth step
      after = case stepAfter step of
                Just afterExpr -> object . assignHoleResToJSON . assignHoleIds $ afterExpr
                Nothing -> before
   in
  object
    [ "index" .= i,
      "focus" .= prettyShow (focusExpr (stepFocus step)),
      "before" .= before,
      "focusedRange" .= fmap focusRangeToJSON focusedRange,
      "context" .= prettyShowContext (stepContext step),
      "after" .= after,
      "focusKind" .= focusKind (stepFocus step)
    ]
  where
    focusKind (Redex _) = "redex" :: T.Text
    focusKind (ROpCall _ _) = "opcall" :: T.Text

    focusPosToJSON :: FocusPos -> A.Value
    focusPosToJSON p =
      object
        [ "line" .= posLine p,
          "column" .= posColumn p,
          "offset" .= posOffset p
        ]

    focusRangeToJSON :: FocusRange -> A.Value
    focusRangeToJSON r =
      object
        [ "start" .= focusPosToJSON (rangeStart r),
          "end" .= focusPosToJSON (rangeEnd r)
        ]

resWithStepsToJSON :: (Either (String, Int) (Expr Id), [Step Id]) -> A.Value
resWithStepsToJSON c = object $ case c of
    (Right c', steps) -> stepsRes steps 0 ++ assignHoleResToJSON (assignHoleIds c')
    (Left (err, code), steps) -> stepsRes steps code ++ ["error" .= err]
  where 
    stepsRes :: [Step Id] -> Int -> [Pair]
    stepsRes steps status = 
      [ "steps" .= zipWith stepToJSON [0 ..] steps,
        "stepCount" .= length steps,
        "status" .= status ]

errorToJSON :: String -> Int -> A.Value
errorToJSON err code = object [ "error" .= err, "status" .= code ]

putJSON :: A.Value -> IO ()
putJSON = BSL.putStrLn . A.encode

requestLogPath :: FilePath
requestLogPath = "effhole-request-log.jsonl"

persistRequestJSON :: BSL.ByteString -> IO ()
persistRequestJSON body =
  appendFile requestLogPath (BSL.unpack body ++ "\n") `catch` handler
  where
    handler :: SomeException -> IO ()
    handler err = hPutStrLn stderr $ "Failed to persist request log: " ++ show err

data Mode = Eval Int | Norm Int | EvalStep Int | NormStep Int

-- TODO: make a real LSP server
data Request = Request
  { command :: T.Text
  , content :: Maybe T.Text
  , fuel :: Maybe Int
  , holeName :: Maybe T.Text
  , holeContext :: Maybe A.Value
  , username :: Maybe T.Text
  , timestamp :: Maybe Integer
  } deriving (Show, Generic)
instance FromJSON Request where
  parseJSON = withObject "Request" $ \v ->
    Request
      <$> v .: "command"
      <*> v .:? "content"
      <*> v .:? "fuel"
      <*> v .:? "holeName"
      <*> v .:? "holeContext"
      <*> v .:? "username"
      <*> v .:? "timestamp"

server :: T.Text -> IO()
server input = putJSON $ runRequestJSON (BSL.pack (T.unpack input))

runRequestJSON :: BSL.ByteString -> A.Value
runRequestJSON input =
  case A.eitherDecode input :: Either String Request of
    Left err -> errorToJSON err (-1)
    Right req -> runRequest req

requireContent :: Request -> (T.Text -> A.Value) -> A.Value
requireContent req f =
  case content req of
    Nothing -> errorToJSON "Missing field: content" 4
    Just text -> f text

requireFuel :: Request -> (Int -> A.Value) -> A.Value
requireFuel req f =
  case fuel req of
    Nothing -> errorToJSON "Missing field: fuel" 4
    Just n -> if n > 0 && n <= maxFuel then f n
              else errorToJSON "Invalid fuel value" 5
  where
    maxFuel = 2000  -- Set a reasonable upper limit for fuel to prevent abuse

withParsedProgram :: Request -> ((E.Expr, M.Map CodePos String) -> A.Value) -> A.Value
withParsedProgram req f =
  requireContent req $ \text ->
    case parseProgram text of
      Left err -> errorToJSON err 1
      Right parsed -> f (normalizeParsedProgram parsed)

withParsedAndFuel :: Request -> (Int -> E.Expr -> A.Value) -> A.Value
withParsedAndFuel req f = requireFuel req $ \n -> withParsedProgram req $ \(e, _) -> f n e

runRequest :: Request -> A.Value
runRequest req =
  case command req of
    "getHoleID" -> withParsedProgram req $ \(_, m) -> object [ "holeMap" .= m, "status" .= (0 :: Int) ]
    "logHoleClick" -> object [ "ack" .= True, "status" .= (0 :: Int) ]
    "eval" ->
      withParsedAndFuel req $ \n e ->
        case runEvalWithFuel n (elaborate e) of
          Left err -> errorToJSON err 2
          Right Nothing -> errorToJSON "Evaluation fuel exhausted" 3
          Right (Just c') -> object $ assignHoleResToJSON (assignHoleIds c') ++ successStatus
    "evalStep" -> withParsedAndFuel req $ \n e -> resWithStepsToJSON . runEvalWithStepsFuel n $ elaborate e
    "norm" ->
      withParsedAndFuel req $ \n e ->
        case norm n (elaborate e) of
          Nothing -> errorToJSON "Normalization fuel exhausted" 3
          Just c' -> object $ assignHoleResToJSON (assignHoleIds c') ++ successStatus
    "normStep" -> withParsedAndFuel req $ \n e -> resWithStepsToJSON . normWithSteps n $ elaborate e
    _ -> errorToJSON "Unknown command" (-2)

statusFromResultCode :: Int -> Status
statusFromResultCode code = case code of
  0 -> status200
  (-1) -> status400
  4 -> status400
  5 -> status400
  _ -> status422

statusFromResponse :: A.Value -> Status
statusFromResponse value =
  case parseMaybe (withObject "Response" (.:? "status")) value of
    Just (Just code) -> statusFromResultCode code
    _ -> status422

httpApp :: Maybe BS.ByteString -> Application
httpApp basePath req respond = 
  case (requestMethod req, path) of
    (m, p) | m == postMethod && p == runPath -> do
      body <- strictRequestBody req
      persistRequestJSON body
      let result = runRequestJSON body
      respondJson (statusFromResponse result) result
    (m, p) | m == getMethod && p == healthPath ->
      respondJson status200 (object ["ok" .= True])
    (m, p) | p == runPath && m /= postMethod ->
      respondJson status405 (object ["error" .= ("Method not allowed" :: String)])
    _ ->
      respondJson status404 (object ["error" .= ("Not found" :: String)])
  where
    path = normalizeProxyPath basePath (rawPathInfo req)
    jsonHeader = (hContentType, BS.pack "application/json")
    respondJson status body = respond $ responseLBS status [jsonHeader] (A.encode body)
    postMethod = BS.pack "POST"
    getMethod = BS.pack "GET"
    runPath = BS.pack "/api/v1/run"
    healthPath = BS.pack "/health"

normalizeProxyPath :: Maybe BS.ByteString -> BS.ByteString -> BS.ByteString
normalizeProxyPath Nothing p = p
normalizeProxyPath (Just base) p
  | p == base = BS.pack "/"
  | withSlash `BS.isPrefixOf` p = BS.drop (BS.length base) p
  | otherwise = p
  where
    withSlash = BS.snoc base '/'

normalizeBasePath :: Maybe String -> Maybe BS.ByteString
normalizeBasePath Nothing = Nothing
normalizeBasePath (Just raw)
  | BS.null cleaned = Nothing
  | otherwise = Just withLeadingSlash
  where
    -- Accept values like "effhole", "/effhole" or "/effhole/" and normalize to "/effhole".
    cleaned = BS.dropWhileEnd (== '/') . BS.dropWhile (== '/') $ BS.pack raw
    withLeadingSlash = BS.cons '/' cleaned

runHttpServer :: Int -> Maybe String -> IO ()
runHttpServer port basePath = do
  putStrLn $ "EffHole HTTP Server running on port " ++ show port
  case normalizeBasePath basePath of
    Just p -> putStrLn $ "Base path: " ++ BS.unpack p
    Nothing -> putStrLn "No base path configured, accepting requests at root path"
  run port (httpApp (normalizeBasePath basePath))
