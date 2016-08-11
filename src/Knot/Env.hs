{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

module Knot.Env where

import Knot.Common

import           Control.Applicative
import           Control.Monad.Error.Class
import           Control.Monad.Reader.Class
import           Control.Monad.Trans.Reader (ReaderT, runReaderT)
import           Control.Monad.Trans.Class
import           Data.Map (Map)
import qualified Data.Map as M
import           Text.Show.Pretty

--------------------------------------------------------------------------------

data GlobalEnv =
  GlobalEnv
  { envNamespaceSort   :: Map NamespaceTypeName (Maybe SortTypeName)
  , envFunctionType    :: Map FunName (SortTypeName, [NamespaceTypeName])
  , envEnvClause       :: Map
                            (EnvTypeName, NamespaceTypeName)
                            ([FieldTypeName 'WOMV], Maybe RelationTypeName)
  , envRelationType    :: Map
                            RelationTypeName
                            (Maybe EnvTypeName, [FieldTypeName 'WOMV])
  , envNamespaceRoots  :: Map NamespaceTypeName [NameRoot]
  , envSortRoots       :: Map SortTypeName [NameRoot]
  , envEnvRoots        :: Map EnvTypeName [NameRoot]
  , envRelationRoots   :: Map RelationTypeName [NameRoot]
  , envSetRoots        :: Map SetTypeName [NameRoot]
  , envCtorType        :: Map CtorName SortTypeName
  -- , envRelationOutput :: Map (FunName, RelationTypeName) EnvTypeName
  , envRelationOutputs :: Map RelationTypeName [(FunName, EnvTypeName)]
  , envSortCtors       :: Map SortTypeName [CtorName]
  -- , envNameRoot :: Map NameRoot ResolvedTypeName
  }
  deriving Show

newtype EnvT m a = EnvT { fromEnvT :: ReaderT GlobalEnv m a }
  deriving (Functor, Applicative, Monad, MonadError e, MonadTrans, FreshM)

lookupEnv :: (Show r, Show k, Applicative m, MonadError String m, MonadReader r m, Ord k) => k -> (r -> Map k b) -> String -> m b
lookupEnv k acc s = do
  r <- ask
  case  M.lookup k (acc r) of
    Just mbStn -> pure mbStn
    Nothing -> throwError $ unlines
                 [ s ++ ": cannot find " ++ show k
                 , ppShow r
                 ]

instance (Applicative m, MonadError String m) => EnvM (EnvT m) where
  lookupNamespaceSort ntn = EnvT $ lookupEnv ntn envNamespaceSort
      "Knot.Env.EnvM(EnvT).lookupNamespaceSort"
  lookupFunctionType fn = EnvT $ lookupEnv fn envFunctionType
      "Knot.Env.EnvM(EnvT).lookupFunctionType"
  lookupEnvClause etn ntn = EnvT $ lookupEnv (etn,ntn) envEnvClause
      "Knot.Env.EnvM(EnvT).lookupEnvClause"
  lookupRelationType rtn = EnvT $ lookupEnv rtn envRelationType
      "Knot.Env.EnvM(EnvT).lookupRelationType"
  lookupNamespaceRoots ntn = EnvT $ lookupEnv ntn envNamespaceRoots
      "Knot.Env.EnvM(EnvT).lookupNamespaceRoots"
  lookupSortRoots stn = EnvT $ lookupEnv stn envSortRoots
      "Knot.Env.EnvM(EnvT).lookupSortRoots"
  lookupEnvRoots etn = EnvT $ lookupEnv etn envEnvRoots
      "Knot.Env.EnvM(EnvT).lookupEnvRoots"
  lookupRelationRoots rtn = EnvT $ lookupEnv rtn envRelationRoots
      "Knot.Env.EnvM(EnvT).lookupRelationRoots"
  lookupSetRoots ztn = EnvT $ lookupEnv ztn envSetRoots
      "Knot.Env.EnvM(EnvT).lookupSetRoots"
  lookupCtorType cn = EnvT $ lookupEnv cn envCtorType
      "Knot.Env.EnvM(EnvT).lookupCtorType"
  -- lookupRelationOutput fn rtn = EnvT $ lookupEnv (fn,rtn) envRelationOutput
  --     "Knot.Env.EnvM(EnvT).lookupRelationOutput"
  lookupRelationOutputs k = EnvT $ lookupEnv k envRelationOutputs
      "Knot.Env.EnvM(EnvT).lookupRelationOutputs"
  lookupSortCtors k = EnvT $ lookupEnv k envSortCtors
      "Knot.Env.EnvM(EnvT).lookupSortCtors"
  -- lookupNameRoot k = EnvT $ lookupEnv k envNameRoot
  --     "Knot.Env.EnvM(EnvT).lookupNameRoot"

runEnvT :: EnvT m a -> GlobalEnv -> m a
runEnvT = runReaderT . fromEnvT
