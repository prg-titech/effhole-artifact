module CLI where

import Options.Applicative hiding (liftIO)
import Server hiding (command)
import qualified Data.Text.IO as TIO
import qualified Data.Text as T
import Internal (runEvalWithFuel, prettyShow)
import Parser (parseProgram)
import Elaboration (elaborate)
import Control.Monad.IO.Class (liftIO)
import System.Console.Haskeline

data Command
  = Repl
  | Run FilePath
  | LSPServer Int
  | Server
  | HttpServer Int (Maybe String)

-- 1. interpreter mode
runParser :: Parser Command
runParser = Run <$> strArgument (metavar "FILE" <> help "Source file to run")

-- 2. server mode
serverParser :: Parser Command
serverParser = LSPServer 
  <$> option auto (long "port" <> short 'p' <> value 8080 <> help "LSP Server port")

httpParser :: Parser Command
httpParser = HttpServer
  <$> option auto (long "port" <> short 'p' <> value 8081 <> help "HTTP server port")
  <*> optional (strOption (long "base-path" <> short 'b' <> metavar "PATH" <> help "Optional deployment path prefix, e.g. /effhole"))

subcommandParser :: Parser Command
subcommandParser = hsubparser
  (  command "repl" (info (pure Repl) (progDesc "Start the REPL"))
  <> command "run"  (info runParser  (progDesc "Run a script file"))
  <> command "lsp"  (info serverParser (progDesc "Start the language server"))
  <> command "server" (info (pure Server) (progDesc "Start the server without LSP"))
  <> command "http" (info httpParser (progDesc "Start the HTTP JSON server"))
  )

doServer :: IO ()
doServer = do
  input <- TIO.getContents
  server input

-- 1. REPL mode
replFuel :: Int
replFuel = 2000  -- same upper limit as the HTTP server's maxFuel

evalReplLine :: T.Text -> IO ()
evalReplLine input =
  case parseProgram input of
    Left err -> putStrLn ("Parse error: " ++ err)
    Right parsed ->
      let (e, _) = normalizeParsedProgram parsed
       in case runEvalWithFuel replFuel (elaborate e) of
            Left err -> putStrLn ("Error: " ++ err)
            Right Nothing -> putStrLn "Evaluation fuel exhausted"
            Right (Just result) -> putStrLn (prettyShow result)

repl :: IO ()
repl = runInputT defaultSettings $ do
  outputStrLn "EffHole REPL — type an expression to evaluate, :quit to exit."
  loop
  where
    loop = do
      minput <- getInputLine "> "
      case minput of
        Nothing -> pure ()  -- EOF (Ctrl-D)
        Just input ->
          case trim input of
            ":quit" -> pure ()
            ":q"    -> pure ()
            ""      -> loop
            line    -> liftIO (evalReplLine (T.pack line)) >> loop
    trim = T.unpack . T.strip . T.pack

cli :: IO ()
cli = do
  cmd <- execParser opts
  case cmd of
    Repl          -> repl
    Run f         -> putStrLn $ "Running file: " ++ f -- TODO: implement file execution
    LSPServer p   -> putStrLn $ "LSP listening on port " ++ show p -- TODO: implement LSP server
    Server        -> doServer
    HttpServer p basePath -> runHttpServer p basePath
  where
    opts = info (subcommandParser <**> helper)
      (fullDesc <> progDesc "EffHole CLI" <> header "effhole - a language with effect holes")
