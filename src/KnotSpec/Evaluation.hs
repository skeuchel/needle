{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

module KnotSpec.Evaluation where

import           Knot.Env
import           KnotSpec.Inference
import           KnotSpec.Substitution
import           KnotSpec.Syntax

import           Control.Monad.Error.Class
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.Reader (ReaderT, runReaderT)
import           Control.Monad.Trans.State.Strict (StateT)
import           Data.Map (Map)
import qualified Data.Map as M

--------------------------------------------------------------------------------

class (Applicative m, MonadError String m) => EvalM m where
  lookupFunctionCase  :: FunName -> CtorName -> m ([FunField 'Checked], BindSpec 'Checked)

instance EvalM m => EvalM (ReaderT s m) where
  lookupFunctionCase = (lift.) . lookupFunctionCase
instance EvalM m => EvalM (StateT s m) where
  lookupFunctionCase = (lift.) . lookupFunctionCase

deriving instance EvalM m => EvalM (InfT m)

--------------------------------------------------------------------------------

symEvalBindSpec :: EvalM m =>
  BindSpec 'Checked -> Substitution 'ResolvedVars -> BindSpec 'Checked -> m (BindSpec 'Checked)
symEvalBindSpec bs0 _sub Nil = pure bs0
symEvalBindSpec bs0 sub (bs :. bsi) = do
  bs' <- symEvalBindSpec bs0 sub bs
  case bsi of
    BsiBinding bv | Just bv' <- M.lookup bv (subBindingVariables sub) ->
      pure (bs' :. BsiBinding bv')
    BsiCall fn sv | Just st <- M.lookup sv (subSortVariables sub) ->
      symEvalFun bs' fn st
    _ -> throwError "KnotSpec.Evaluation.symEvalBindSpec"

symEvalFun :: EvalM m => BindSpec 'Checked -> FunName -> SymbolicTerm 'ResolvedVars -> m (BindSpec 'Checked)
symEvalFun bs0 fn st = case st of
  SymVar () sv -> pure (bs0 :. BsiCall fn sv)
  SymWeaken{} -> throwError "KnotSpec.Evaluation.symEvalFun.SymWeaken"
  SymSubst{} -> throwError "KnotSpec.Evaluation.symEvalFun.SymSubst"
  SymCtorVarFree{} -> throwError "KnotSpec.Evaluation.symEvalFun.SymCtorVarFree"
  SymCtorVarBound{} -> throwError "KnotSpec.Evaluation.symEvalFun.SymCtorVarBound"
  SymCtorReg () cn sfs -> do
    (ffs,rhs) <- lookupFunctionCase fn cn
    sub <- makeFunSubstitution ffs sfs
    symEvalBindSpec bs0 sub rhs

--------------------------------------------------------------------------------

data EvalEnv =
  EvalEnv
  { envFunctionCase :: Map (FunName,CtorName) ([FunField 'Checked], BindSpec 'Checked)
  }
  deriving Show

makeEvalEnv :: [FunDecl 'Checked] -> EvalEnv
makeEvalEnv fds =
  EvalEnv
    (M.fromList
       [ ((fdName fd, fcCtor fc), (fcFields fc, fcRhs fc))
       | fd <- fds, fc <- fdCases fd
       ])

newtype EvalT m a = EvalT { fromEvalT :: ReaderT EvalEnv m a }
  deriving (Functor, Applicative, Monad, MonadError e, MonadTrans, EnvM)

instance (Applicative m, MonadError String m) => EvalM (EvalT m) where
  lookupFunctionCase fn cn = EvalT $ lookupEnv (fn,cn) envFunctionCase
      "KnotSpec.checkSorts.TcM(Tc).lookupFunctionCase"

runEvalT :: EvalT m a -> EvalEnv -> m a
runEvalT = runReaderT . fromEvalT
