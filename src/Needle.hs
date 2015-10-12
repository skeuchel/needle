
import           Data.List

import           System.Directory
import           System.Environment
import           System.FilePath
import           System.IO

import           Text.Printf
import           Text.Parsec.String
import           Text.Show.Pretty

import qualified KnotSpec.Parser as IS
import qualified KnotSpec.Syntax as IS
import qualified KnotSpec.AG as IS

import qualified KnotCore.Syntax as IC
import qualified KnotCore.Environment as IC
import qualified KnotCore.Elaboration as IC

-- import qualified Coq.Syntax as Coq
-- import qualified Coq.AG as Coq
-- import qualified Coq.Pretty.Common as Coq
import qualified Coq.Pretty as Coq

main :: IO ()
main = do
  args <- getArgs
  case args of
   [fp] -> do
     ex <- doesFileExist fp
     if ex
       then do
         result <- parseFromFile IS.pSpecification fp
         case result of
           Left err   -> hPrint stderr err
           Right spec -> process fp spec
       else usage
   _ -> usage
  return ()

usage :: IO ()
usage = do
  prog <- getProgName
  hPutStrLn stderr $ printf "Usage: %s <filename>" prog

process :: FilePath -> IS.TermSpec -> IO ()
process fp spec =
  do
    -- putStrLn "Original spec:"
    -- putStrLn (ppShow spec)
    -- putStrLn ""

    case IS.desugarTermSpec spec of
      Left err -> hPutStrLn stderr $ "Error: " ++ err
      Right coreSpec -> do
        let elaborated   = IC.elaborateSpec coreSpec
            printed      = Coq.pretty elaborated

        -- putStrLn "Raw core spec:"
        -- putStrLn (ppShow coreSpec)
        -- putStrLn ""

        -- putStrLn "Namespaced core spec:"
        -- putStrLn (ppShow namespaced)
        -- putStrLn ""

        -- putStrLn "Core spec environments:"
        -- putStrLn (ppShow (IC.metaEnvironments coreSpec))
        -- putStrLn ""

        -- putStrLn "Elaborated coq code:"
        -- putStrLn (ppShow elaborated)
        -- putStrLn ""

        -- putStrLn "Pretty printed:"
        withFile (replaceExtension fp ".v") WriteMode
          (\h -> Coq.hPutDoc h printed)
