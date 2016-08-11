{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

module KnotSpec.CheckSorts where

import           Knot.Env
import           KnotSpec.Evaluation
import           KnotSpec.Inference
import           KnotSpec.Renaming
import           KnotSpec.Syntax

import           Control.Monad
import           Control.Monad.Error.Class
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.Reader (ReaderT, runReaderT)
import           Control.Monad.Trans.State.Strict (StateT)
import           Data.Foldable
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Traversable

--------------------------------------------------------------------------------

class (MonadError String m, EnvM m) => TcM m where
  lookupFunctionCases :: CtorName -> m [(FunName, [FunField 'ResolvedVars], BindSpec 'ResolvedVars)]

instance TcM m => TcM (StateT s m) where
  lookupFunctionCases = lift . lookupFunctionCases
instance TcM m => TcM (ReaderT r m) where
  lookupFunctionCases = lift . lookupFunctionCases

deriving instance TcM m => TcM (InfT m)
deriving instance TcM m => TcM (EvalT m)

--------------------------------------------------------------------------------

checkSortDecl :: TcM m => SortDecl 'ResolvedVars -> m (SortDecl 'Checked)
checkSortDecl (SortDecl stn nrs cds) =
  SortDecl stn nrs <$> traverse (checkCtorDecl stn) cds

checkCtorDecl :: TcM m => SortTypeName -> CtorDecl 'ResolvedVars -> m (CtorDecl 'Checked)
checkCtorDecl stn (CtorVar cn fv) = do
  let fun = "KnotSpec.CheckSorts.checkCtorDecl"
  mbStn' <- lookupNamespaceSort (typeNameOf fv)
  case mbStn' of
    Just stn'
      | stn == stn' -> pure (CtorVar cn fv)
      | otherwise   -> throwError $ fun ++ ".CtorVar: " ++ show (cnLoc cn)
    Nothing -> throwError $ fun ++ ".CtorVar"
checkCtorDecl _stn (CtorReg cn fds) = do
  -- let fun = "KnotSpec.CheckSorts.checkCtorDecl"
  lenv <- flip execInfT defaultInfState $ do
    for_ fds $ \fd -> case fd of
      FieldDeclSort _loc bs sv -> infBindSpec Nil bs >>= checkSubtreeBindSpec sv
      FieldDeclEnv _loc bs ev -> infBindSpec Nil bs >>= checkEnvBindSpec ev
      -- Bindings do not have any explicit binding specifications in the surface
      -- language but only unification variables from the annotation step. It
      -- does not add any valuable information to the scope inference.
      FieldDeclBinding{}   -> return ()
      -- References are always in the outer scope.
      FieldDeclReference{} -> return ()
      FieldDeclSet{} -> return ()

    cases <- lookupFunctionCases cn
    for_ cases $ \(_fn,ffs,rhs) -> do
      ren <- makeRenaming ffs fds
      rhs' <- renameBindSpec ren rhs
      void (infBindSpec Nil rhs')

  CtorReg cn <$> traverse (checkFieldDecl lenv) fds

checkFieldDecl :: TcM m =>
  InfState -> FieldDecl w 'ResolvedVars 'ResolvedVars ->
  m (FieldDecl w 'Checked 'Checked)
checkFieldDecl lenv fd =
  let fun = "KnotSpec.CheckSorts.checkFieldDecl" in case fd of
  FieldDeclSort loc _bs sv ->
    case M.lookup sv (_infSortVariables lenv) of
      Just bs' -> pure (FieldDeclSort loc bs' sv)
      Nothing  -> throwError $ fun ++ ".CtorReg.FieldDeclSort"
  FieldDeclEnv loc _bs ev ->
    case M.lookup ev (_infEnvVariables lenv) of
      Just bs' -> pure (FieldDeclEnv loc bs' ev)
      Nothing  -> throwError $ fun ++ ".CtorReg.FieldDeclEnv"
  FieldDeclBinding loc _bs bv ->
    case M.lookup bv (_infBindingVariables lenv) of
      Just bs' -> pure (FieldDeclBinding loc bs' bv)
      Nothing  -> throwError $ fun ++ ".CtorReg.FieldDeclBinding"
  FieldDeclReference loc fv -> pure (FieldDeclReference loc fv)
  FieldDeclSet loc zv -> pure (FieldDeclSet loc zv)

checkEnvDecl :: TcM m =>
  EnvDecl 'ResolvedVars -> m (EnvDecl 'Checked)
checkEnvDecl (EnvDecl etn nrs ecds) =
  EnvDecl etn nrs <$> traverse checkEnvCtorDecl ecds

checkEnvCtorDecl :: TcM m =>
  EnvCtorDecl 'ResolvedVars -> m (EnvCtorDecl 'Checked)
checkEnvCtorDecl (EnvCtorNil cn) = pure (EnvCtorNil cn)
checkEnvCtorDecl (EnvCtorCons cn bv fds mbRtn) = do
  lenv <- flip execInfT defaultInfState $ do
    checkBindingBindSpec bv Nil
    for_ fds $ \fd -> case fd of
      FieldDeclSort _loc bs sv -> infBindSpec Nil bs >>= checkSubtreeBindSpec sv
      FieldDeclEnv _loc bs ev -> infBindSpec Nil bs >>= checkEnvBindSpec ev
      FieldDeclSet{} -> return ()
  fds' <- traverse (checkFieldDecl lenv) fds
  pure $! EnvCtorCons cn bv fds' mbRtn

--------------------------------------------------------------------------------

data TcEnv =
  TcEnv
  { envFunctionCases :: Map CtorName [(FunName, [FunField 'ResolvedVars], BindSpec 'ResolvedVars)]
  }
  deriving Show

makeTcEnv ::
  [SortDecl 'ResolvedVars] ->
  [FunDecl 'ResolvedVars] -> TcEnv
makeTcEnv sds fds =
  TcEnv
    (M.unionWith (++)
       (M.fromList
         [ (ctorDeclName cd, [])
         | sd <- sds, cd <- sdCtors sd
         ]
       )
       (M.fromListWith (++)
         [ (fcCtor fc, [(fdName fd, fcFields fc, fcRhs fc)])
         | fd <- fds, fc <- fdCases fd
         ])
    )

newtype TcT m a = TcT { fromTcT :: ReaderT TcEnv m a }
  deriving (Functor, Applicative, Monad, MonadError e, MonadTrans, EnvM)

instance (MonadError String m, EnvM m) => TcM (TcT m) where
  lookupFunctionCases cn = TcT $ lookupEnv cn envFunctionCases
      "KnotSpec.CheckSorts.TcM(TcT).lookupFunctionCases"

runTcT :: TcT m a -> TcEnv -> m a
runTcT = runReaderT . fromTcT
