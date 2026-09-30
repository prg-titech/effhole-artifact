{-# LANGUAGE OverloadedStrings #-}

module Parser where

import Common
import Control.Monad
import Control.Monad.State 
import qualified Data.Text as T
import Data.Void
import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Control.Monad.Combinators.Expr
import External
import Type
import qualified Data.Map as M

data ParserState = ParserState
  { holeId :: Int
  , holeIdMap :: M.Map CodePos Int  -- from (line, column) to hole name
  } deriving (Show, Eq)

type Parser = ParsecT Void Id (State ParserState)

sc :: Parser ()
sc =
  L.space
    space1
    (L.skipLineComment "//")
    (L.skipBlockComment "/*" "*/")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: Id -> Parser Id
symbol = L.symbol sc

-- lexical tokens
integer :: Parser Int
integer = lexeme (L.signed sc L.decimal)

-- signedInteger :: Parser Int
-- signedInteger = L.signed sc integer

reservedWords :: [String]
reservedWords = ["True", "False", "handler", "do", "match", "with", "handle", "if", "then", "else"
                , "inl", "inr", "def", "val"]

identifier :: Parser Id
identifier = lexeme identifier_

-- consume no whitespace after the identifier, used for parsing operation names
identifier_ :: Parser Id
identifier_ = T.pack <$> identifier' <|> string "$"  -- HACK: fix it
  where
    identifier' :: Parser String
    identifier' = do
      identName <- (:) <$> letterChar <*> many alphaNumChar
      check identName

    check x = if x `elem` reservedWords
                then fail $ "reserved word " ++ show x ++ " cannot be an identifier"
                else return x

symbolicKeyword :: Id -> Parser ()
symbolicKeyword keyword = lexeme $ try $ do
  _ <- string keyword
  notFollowedBy alphaNumChar

parens :: Parser a -> Parser a
parens    = between (symbol "(") (symbol ")")

braces :: Parser a -> Parser a
braces    = between (symbol "{") (symbol "}")

brackets :: Parser a -> Parser a
brackets  = between (symbol "[") (symbol "]")

semicolon :: Parser Id
semicolon = symbol ";"
comma :: Parser Id
comma     = symbol ","
colon :: Parser Id
colon     = symbol ":"
dot :: Parser Id
dot       = symbol "."

parse2tuple :: (a -> a -> b) -> Parser a -> Parser b
parse2tuple f parser = parens $ do
  a <- parser
  void comma
  b <- parser
  return (f a b)

toCodePos :: SourcePos -> CodePos
toCodePos pos = (unPos $ sourceLine pos, unPos $ sourceColumn pos)

parseBindVar :: Parser BindVar
parseBindVar = do
  srcStart <- getSourcePos
  x <- identifier_
  srcEnd <- getSourcePos
  sc
  return $ BindVar x (toCodePos srcStart) (toCodePos srcEnd)

-- parser
-- atomic expressions
parseAtom :: Parser Expr
parseAtom = choice
  [ parseDo <?> "do expression"
  , parseAtomNoDo
  ]

parseAtomNoDo :: Parser Expr
parseAtomNoDo = choice
  [ parseInt <?> "integer literal"
  , parseBool <?> "boolean literal"
  , parseUnit <?> "unit literal"
  , parseString <?> "string literal"
  , parseHole <?> "hole"
  , parseParenOrPair
  , parseHandler <?> "handler expression"
  , parseInLorR <?> "sum injection"
  , parseIf <?> "if expression"
  , parseWith <?> "with-handle expression"
  , parseNil <?> "empty list"
  , parseOpCall <?> "operation call"
  , parseVar <?> "variable"
  ]

parseParenOrPair :: Parser Expr
parseParenOrPair = between (symbol "(") (symbol ")") body <?> "parenthesized expression"
  where
    body = do
      e1 <- parseExpr
      (do
          void comma
          Pair e1 <$> parseExpr
        ) <|> pure e1

operatorTable :: [[Operator Parser Expr]]
operatorTable =
  [ [ InfixL (BiOp Mul <$ symbol "*")
    , InfixL (BiOp Div <$ try (symbol "/" <* notFollowedBy (char '='))) ]
  , [ InfixL (BiOp Add <$ symbol "+")
    , InfixL (BiOp Sub <$ symbol "-") ]
  , [ InfixR (Cons <$ symbol "::") ]
  , [ InfixL (BiOp Eqi <$ symbol "==")
    , InfixL (BiOp Neq <$ symbol "/=")
    , InfixL (BiOp Le <$ try (symbol "<=") )
    , InfixL (BiOp Lt <$ try (symbol "<" <* notFollowedBy (char '=')))
    , InfixL (BiOp Ge <$ try (symbol ">=") )
    , InfixL (BiOp Gt <$ try (symbol ">" <* notFollowedBy (char '='))) ]
  , [ InfixL (BiOp Concat <$ symbol "^") ]
  ]

-- application is a head expression followed by one or more parenthesized arguments.
-- This keeps implicit juxtaposition out of the grammar.
parseApp = do
  first <- parseAtomNoDo
  others <- many (parens parseExpr <?> "application argument")
  return $ foldl App first others

parseExpr :: Parser Expr
parseExpr = makeExprParser parseExpr' operatorTable
  where
    parseExpr' = choice [ parseAbs <?> "lambda abstraction"
                        , parseDo <?> "do expression"
                        , parsePrefixMatch
                        , parseAppWithMatch ]

    parsePrefixMatch = do
      void (symbolicKeyword "match")
      fail "match is a postfix form: write <scrutinee> match { ... }"

    parseAppWithMatch = do
      scrutinee <- parseApp
      parseMatchSuffix scrutinee <|> pure scrutinee

    parseMatchSuffix scrutinee = do
      void (symbolicKeyword "match")
      braces $ choice
        [ lookAhead (symbolicKeyword "[]") *> parseUnconsBody scrutinee
        , lookAhead (try $ parseBindVar *> symbolicKeyword "::") *> parseUnconsBody scrutinee
        , lookAhead (symbolicKeyword "inl" <|> symbolicKeyword "inr") *> parseUneitherBody scrutinee
        , parseUnpairBody scrutinee
        ]

parseInt = NV <$> integer

parseBool :: Parser Expr
parseBool = symbolicKeyword "True" *> pure (BV True)
        <|> symbolicKeyword "False" *> pure (BV False)

parseString :: Parser Expr
parseString = Str <$> lexeme (char '"' *> manyTill L.charLiteral (char '"'))

parseVar = Var <$> identifier

parseUnit :: Parser Expr
parseUnit = symbol "()" *> pure Unit

parseNil = symbolicKeyword "[]" *> pure Nil

-- parseUnCons is now called by parseMatch
-- Extract just the body parsing logic
parseUnconsBody e1 = do
  b1 <- parseBranch
  void semicolon
  b2 <- parseBranch
  void $ optional semicolon
  case (b1, b2) of
    (Left eNil, Right (h, t, eCons)) -> return $ UnCons e1 eNil h t eCons
    (Right (h, t, eCons), Left eNil) -> return $ UnCons e1 eNil h t eCons
    _ -> fail "match expression for lists must have one [] case and one :: case"
  where
    parseBranch = try branchNil <|> branchCons
    branchNil = do
      symbolicKeyword "[]"
      symbolicKeyword "=>"
      e <- parseExpr
      return (Left e)
    branchCons = do
      h <- parseBindVar
      symbolicKeyword "::"
      t <- parseBindVar
      symbolicKeyword "=>"
      e <- parseExpr
      return (Right (h, t, e))

parseAbs = do
  void (symbol "\\")
  firstParam <- parseBindVar <?> "lambda parameter"
  restParams <- many (try (lookAhead binderStart *> parseBindVar <?> "lambda parameter"))
  void (dot <?> "'.' after lambda parameters")
  e <- parseExpr
  return $ case e of
    Abs y ys body -> Abs firstParam (restParams ++ (y : ys)) body
    _ -> Abs firstParam restParams e
  where
    binderStart :: Parser Char
    binderStart = letterChar <|> char '$'

parsePair = parse2tuple Pair parseExpr

parseInLorR = do
  b <- symbolicKeyword "inl" *> pure True <|> symbolicKeyword "inr" *> pure False
  InLorR b <$> parseExpr

-- parseUnEither is now called by parseMatch
-- Extract just the body parsing logic
parseUneitherBody scrutinee = do
  b1 <- parseBranch
  void semicolon
  b2 <- parseBranch
  void $ optional semicolon
  case (b1, b2) of
    ((True, id1, e1), (False, id2, e2)) -> return $ UnEither scrutinee id1 e1 id2 e2
    ((False, id2, e2), (True, id1, e1)) -> return $ UnEither scrutinee id1 e1 id2 e2
    _ -> fail "match expression for sum types must have one 'inl' and one 'inr' branch"
  where
    -- support parsing branches in any order. the boolean indicates whether it's an 'inl' branch or 'inr' branch
    parseBranch = do
      isInl <- (symbolicKeyword "inl" >> return True) <|> (symbolicKeyword "inr" >> return False)
      binderId <- parseBindVar
      symbolicKeyword "=>"
      e <- parseExpr
      return (isInl, binderId, e)

parseHandler = symbolicKeyword "handler" >> braces body
  where
    body = do
      x <- parseBindVar
      void (symbol "=>")
      e <- parseExpr
      void semicolon
      hcs <- hcase `sepBy` semicolon
      return (Handler x e hcs)

    hcase = do
      void (optional (symbol "#"))
      op <- identifier
      (x, k) <- parse2tuple (,) parseBindVar
      void (symbol "=>")
      HandlerCase (OpTag op) x k <$> parseExpr

parseHole = do
  SourcePos _ l c <- getSourcePos
  void $ lexeme (char '?') >> optional (L.decimal :: Parser Int)  -- HACK: fix it
  ParserState nextId holeMap <- get
  let newState = ParserState (nextId + 1) (M.insert (unPos l, unPos c) nextId holeMap)
  put newState
  return (ExprHole nextId)
  
parseIf = do
  symbolicKeyword "if"
  e <- parseExpr
  symbolicKeyword "then"
  e1 <- parseExpr
  symbolicKeyword "else"
  e2 <- parseExpr
  return $ If e e1 e2

-- parseUnpair is now called by parseMatch
-- Extract just the body parsing logic
parseUnpairBody p = do
  (a, b) <- parse2tuple (,) parseBindVar
  void (symbolicKeyword "=>")
  Unpair p a b <$> parseExpr

parseOpCall = OpCall <$> parseOperation <*> parens parseExpr
  where
    parseOpHole = OpHole <$> (symbol "?" *> L.decimal)
    parseOperation = do
      void (symbol "#")
      parseOpName <|> parseOpHole

    parseOpName = Operation . OpTag <$> identifier_

parseWith :: Parser Expr
parseWith = do
  void (symbolicKeyword "with")
  h <- parseExpr
  void (symbolicKeyword "handle")
  With h <$> parseExpr

parseDo = do
  braces $ Do <$> many parseStmt <*> parseExpr

parseStmt :: Parser DoStmt
parseStmt = parseLetRec <|> parseValBind <|> try parseExprStmt
  where
    parseLetRec = do
      symbolicKeyword "def"
      f <- parseBindVar
      params <- some (parens parseBindVar)
      symbolicKeyword "="
      e <- parseExpr
      void semicolon
      case params of
        x:xs -> return (LetRec f x xs e)
        [] -> fail "letrec must have at least one parameter"

    parseValBind = do
      symbolicKeyword "val"
      x <- parseBindVar
      symbolicKeyword "="
      e <- parseExpr
      void semicolon
      return $ DoBind x e

    parseExprStmt = DoExpr <$> parseExpr <* semicolon

runStateParser :: Parser a -> T.Text -> (Either (ParseErrorBundle Id Void) a, ParserState)
runStateParser p code = runState (runParserT (sc *> p <* eof) "" code) (ParserState 1 M.empty)
runStateParser' :: Parser a -> T.Text -> Either (ParseErrorBundle Id Void) a
runStateParser' p code = let (res, _) = runStateParser p code in res

parseProgram :: T.Text -> Either String (Expr, M.Map CodePos Int)
parseProgram p = case res of
                   Left err -> Left (errorBundlePretty err)
                   Right e -> Right (e, m)
  where
    (res, ParserState _ m) = runStateParser parseExpr p