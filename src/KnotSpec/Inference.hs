{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

module KnotSpec.Inference where

import           KnotSpec.Syntax

import           Lens.Micro
import           Lens.Micro.Extras
import           Lens.Micro.TH

import           Control.Monad
import           Control.Monad.Error.Class
import           Control.Monad.State.Class
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.State.Strict (StateT, runStateT, execStateT)
import           Data.Map (Map)
import qualified Data.Map as M

--------------------------------------------------------------------------------
-- Local binding inference
--
--   The scope of binding variables of constructors needs to be inferred and
--   checked for consistency. To do so, we traverse the field binding
--   specifications with the assumption that they extend the unary outer scope.
--
--   A local type-inferencing monad 'InfM' keeps the scope of binding
--   variables in a state which can be queried with getBindingBindSpec or
--   updated with insertBindingBindSpec.
--------------------------------------------------------------------------------

class MonadError String m => InfM m where
  checkSubtreeBindSpec :: SortVariable -> BindSpec 'Checked -> m ()
  checkBindingBindSpec :: BindingVariable -> BindSpec 'Checked -> m ()
  checkJudgementBindSpec :: JudgementVariable -> BindSpec 'Checked -> m ()
  checkEnvBindSpec :: EnvVariable -> BindSpec 'Checked -> m ()

infBindSpec :: InfM m =>
  BindSpec 'Checked -> BindSpec 'ResolvedVars -> m (BindSpec 'Checked)
infBindSpec outer Nil = return outer
infBindSpec outer (bs :. bsi) = do
  bs' <- infBindSpec outer bs
  bsi' <- infBindSpecItem bs' bsi
  return (bs' :. bsi')

infBindSpecItem :: InfM m =>
  BindSpec 'Checked -> BindSpecItem 'ResolvedVars -> m (BindSpecItem 'Checked)
infBindSpecItem outer (BsiBinding bv) = do
  checkBindingBindSpec bv outer
  return (BsiBinding bv)
infBindSpecItem outer (BsiCall fn sv) = do
  -- TOREMOVE: This check encodes the restriction that the scope of a function
  -- call should be the scope of the sort field. This should be eventually
  -- lifted when allowing multiple traversals.
  checkSubtreeBindSpec sv outer
  -- (stn,_) <- lookupFunctionType fn
  -- unless
  --   (typeNameOf sv == stn)
  --   (error "KnotSpec.CheckSorts.infBindSpecItem.BsiCall")
  return (BsiCall fn sv)

--------------------------------------------------------------------------------

data InfState =
  InfState
  { _infBindingVariables   :: Map BindingVariable (BindSpec 'Checked)
  , _infSortVariables      :: Map SortVariable (BindSpec 'Checked)
  , _infEnvVariables       :: Map EnvVariable (BindSpec 'Checked)
  , _infJudgementVariables :: Map JudgementVariable (BindSpec 'Checked)
  }

makeLenses ''InfState

defaultInfState :: InfState
defaultInfState = InfState M.empty M.empty M.empty M.empty

newtype InfT m a =
  InfT { fromInfT :: StateT InfState m a }
  deriving (Functor, Applicative, Monad, MonadError e, MonadTrans, EnvM, FreshM)

runInfT :: InfT m a -> InfState -> m (a, InfState)
runInfT = runStateT . fromInfT

execInfT :: Monad m => InfT m a -> InfState -> m InfState
execInfT = execStateT . fromInfT

instance MonadError String m => InfM (InfT m) where
  checkSubtreeBindSpec sv bs = InfT $ do
    mbBs <- gets (M.lookup sv . view infSortVariables)
    case mbBs of
      Just bs' -> when
                    (bs /= bs')
                    (throwError "KnotSpec.Inference.InfM(InfT).checkSubtreeBindSpec")
      Nothing -> modify (infSortVariables %~ M.insert sv bs)
  checkBindingBindSpec bv bs = InfT $ do
    mbBs <- gets (M.lookup bv . view infBindingVariables)
    case mbBs of
      Just bs' -> when
                    (bs /= bs')
                    (throwError "KnotSpec.Inference.InfM(InfT).checkBindingBindSpec")
      Nothing -> modify (infBindingVariables %~ M.insert bv bs)
  checkEnvBindSpec ev bs = InfT $ do
    mbBs <- gets (M.lookup ev . view infEnvVariables)
    case mbBs of
      Just bs' -> when
                    (bs /= bs')
                    (throwError "KnotSpec.Inference.InfM(InfT).checkEnvBindSpec")
      Nothing -> modify (infEnvVariables %~ M.insert ev bs)
  checkJudgementBindSpec jmv bs = InfT $ do
    mbBs <- gets (M.lookup jmv . view infJudgementVariables)
    case mbBs of
      Just bs' -> when
                    (bs /= bs')
                    (throwError "KnotSpec.Inference.InfM(InfT).checkJudgementBindSpec")
      Nothing -> modify (infJudgementVariables %~ M.insert jmv bs)
