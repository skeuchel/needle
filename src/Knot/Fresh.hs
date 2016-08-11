{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Knot.Fresh where

import           Knot.Common

import           Control.Applicative
import           Control.Monad.Error.Class
import           Control.Monad.Reader.Class
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.State.Strict
import           Data.List
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Maybe
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Traversable

--------------------------------------------------------------------------------

newtype FreshT m a =
  FreshT { fromFreshT :: StateT (Map String (Set Suffix)) m a }
  deriving (Functor, Applicative, Monad, MonadError e, MonadReader r, MonadTrans, EnvM)

instance (Applicative m, Monad m) => FreshM (FreshT m) where
  freshenSuffix (NR _loc str) suff = FreshT $ do
    sm <- get
    case M.lookup str sm of
      Nothing -> do
        put (M.insert str (S.singleton suff) sm)
        return suff
      Just ss -> do
        let suff' = chooseSuffix suff ss
        put (M.insert str (S.insert suff' ss) sm)
        return suff'
  localNames m = do
    sm <- FreshT get
    a <- m
    FreshT (put sm)
    return a

chooseSuffix :: Suffix -> Set Suffix -> Suffix
chooseSuffix suff suffs =
  fromMaybe (error "IMPOSSIBLE") $
    find
      (\s -> not (s `S.member` suffs))
      (suff : map show [(0 :: Int)..])

initialNames :: Map String (Set Suffix)
initialNames =
  M.fromList [("S", S.singleton ""),
              ("O", S.singleton ""),
              ("H", S.fromList ["", "0"]),
              ("HS", S.singleton ""),
              ("X", S.fromList ["", "0"])
             ]

runFreshT :: Monad m => FreshT m a -> m a
runFreshT = flip evalStateT initialNames . fromFreshT

--------------------------------------------------------------------------------

freshJudgementVariable :: (EnvM m, FreshM m) =>
  RelationTypeName -> m JudgementVariable
freshJudgementVariable rtn = do
  nrs <- lookupRelationRoots rtn
  let nr = head (nrs ++ [NR LocNoWhere "jm"])
  suff <- freshSuffix nr
  pure $! JV nr suff rtn

freshEnvVariable :: (EnvM m, FreshM m) =>
  EnvTypeName -> m EnvVariable
freshEnvVariable etn = do
  nrs <- lookupEnvRoots etn
  let nr = head (nrs ++ [NR LocNoWhere "e"])
  suff <- freshSuffix nr
  pure $! EV nr suff etn

freshSetVariable :: (EnvM m, FreshM m) =>
  SetTypeName -> m SetVariable
freshSetVariable etn = do
  nrs <- lookupSetRoots etn
  let nr = head (nrs ++ [NR LocNoWhere "e"])
  suff <- freshSuffix nr
  pure $! ZV nr suff etn
