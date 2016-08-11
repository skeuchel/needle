{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}

import qualified Knot.Env as Knot
import qualified Knot.Fresh as Knot
import qualified KnotSpec.Parser as IS
import qualified KnotSpec.Syntax as IS
import qualified KnotSpec.TypeResolution as IS
import qualified KnotSpec.NameResolution as IS
import qualified KnotSpec.Check as IS
import qualified KnotSpec.Group as IS
import qualified KnotSpec.Desugar as IS
import qualified KnotSpec.Environment as IS

import qualified KnotCore.Syntax as IC
import qualified KnotCore.Environment as IC
import qualified KnotCore.Elaboration as IC

import qualified Coq.Syntax as Coq
import qualified Coq.AG as Coq
import qualified Coq.Pretty.Common as Coq
import qualified Coq.Pretty as Coq

import           Options.Applicative as Opts

import           Control.Applicative
import           Control.Monad
import           Control.Monad.Error.Class
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.Except
import           Data.Foldable
import           Data.List
import           Data.Monoid
import           Data.Traversable
import           System.Directory
import           System.Environment
import           System.FilePath
import           System.IO
import           Text.Printf
import           Text.Parsec.String
import           Text.Show.Pretty

--------------------------------------------------------------------------------

data Conf =
  Conf
  { dumpParsed :: Bool
  , dumpTypeResolved :: Bool
  , dumpVarResolved :: Bool
  , dumpChecked :: Bool
  , dumpGrouped :: Bool
  , dumpDesugared :: Bool
  , dumpElaborated :: Bool
  , dumpGlobalEnv :: Bool
  }

pConf :: Opts.Parser Conf
pConf =
  Conf
    <$> switch
          ( long "dump-parsed"
            <> help "Dump AST after parsing"
          )
    <*> switch
          ( long "dump-type-resolved"
            <> help "Dump AST after resolving type names"
          )
    <*> switch
          ( long "dump-var-resolved"
            <> help "Dump AST after resolving variable names"
          )
    <*> switch
          ( long "dump-checked"
            <> help "Dump AST after type checking"
          )
    <*> switch
          ( long "dump-grouped"
            <> help "Dump AST after grouping declarations"
          )
    <*> switch
          ( long "dump-desugared"
            <> help "Dump AST after desugaring"
          )
    <*> switch
          ( long "dump-elaborated"
            <> help "Dump elaborated Coq AST"
          )
    <*> switch
          ( long "dump-global-env"
            <> help "Dump global spec information table"
          )

pOpts :: Opts.Parser (Conf,[FilePath])
pOpts = (,) <$> pConf <*>
  some (argument str (metavar "FILES..."))

desc :: InfoMod a
desc = fullDesc
  -- <> progDesc "Needle desc"
  <> header "needle - infrastructure code generator"

opts :: ParserInfo (Conf,[FilePath])
opts = info (helper <*> pOpts) desc

main :: IO ()
main = do
  (conf,files) <- execParser opts
  traverse_ (process conf) files

process :: Conf -> FilePath -> IO ()
process conf fp = do
  ex <- doesFileExist fp
  unless ex
    (error $ "File does not exist: '" ++ fp ++ "'")

  let dump :: Show a => Bool -> String -> a -> IO ()
      dump False _   _ = return ()
      dump True  ext a =
        withFile
          (replaceExtension fp ext)
          WriteMode
          (flip hPutStrLn $ ppShow a)

  res <- Knot.runFreshT . runExceptT $ do

    parseRes <- lift (lift (parseFromFile IS.pSpecification fp))
    parsed <- case parseRes of
                Left e -> throwError (show e)
                Right r -> pure r
    lift (lift (dump (dumpParsed conf) ".parsed" parsed))

    typeResolved <- withExceptT show $ IS.typeResolution parsed
    lift (lift (dump (dumpTypeResolved conf) ".typeresolved" typeResolved))

    let globalEnv = IS.makeGlobalEnv typeResolved

    lift (lift (dump (dumpGlobalEnv conf) ".globalenv" globalEnv))

    flip Knot.runEnvT globalEnv $ do

      varResolved <- IS.varResolution typeResolved
      lift (lift (lift (dump (dumpVarResolved conf) ".varresolved" varResolved)))

      checked <- IS.check varResolved
      lift (lift (lift (dump (dumpChecked conf) ".checked" checked)))

      let grouped = IS.group checked
      lift (lift (lift (dump (dumpGrouped conf) ".grouped" grouped)))

      desugared <- IS.desugar grouped
      lift (lift (lift (dump (dumpDesugared conf) ".desugared" desugared)))

      elaborated <- IC.elaborateSpec desugared
      lift (lift (lift (dump (dumpElaborated conf) ".elaborated" elaborated)))

      lift (lift (lift (withFile (replaceExtension fp ".v") WriteMode
            (`Coq.hPutDoc` Coq.pretty elaborated))))

  case res of
    Left e -> hPrint stderr e
    Right () -> return ()
