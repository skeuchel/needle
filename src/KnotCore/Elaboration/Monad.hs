{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

module KnotCore.Elaboration.Monad where

import           Knot.Env
import           KnotCore.Environment
import           KnotCore.Syntax

import           Control.Monad
import           Control.Monad.Error.Class
import           Control.Monad.Trans
import           Control.Monad.Trans.Reader (ReaderT(..))
import           Data.Map (Map)
import qualified Data.Map as M

--------------------------------------------------------------------------------

class (EnvM m, FreshM m, MonadError String m) => Elab m where
  getMetaEnvironments    :: m MetaEnvironments
  liftMaybe              :: String -> Maybe a -> m a

instance Elab m => Elab (ReaderT r m) where
  getMetaEnvironments = lift getMetaEnvironments
  liftMaybe str       = lift . liftMaybe str

--------------------------------------------------------------------------------

getSortNamespaceDependencies :: Elab m => SortTypeName -> m [NamespaceTypeName]
getSortNamespaceDependencies stn =
  do
    deps <- meSortNamespaceDeps <$> getMetaEnvironments
    liftMaybe "getSortNamespaceDependencies" (M.lookup stn deps)

getSortRoots             :: Elab m => SortTypeName -> m [NameRoot]
getSortRoots stn =
  do
    nrs <- meSortRoots <$> getMetaEnvironments
    liftMaybe "getSortRoots" (M.lookup stn nrs)

getNamespaceRoots :: Elab m => NamespaceTypeName -> m [NameRoot]
getNamespaceRoots btn =
  do
    nrs <- meNamespaceRoots <$> getMetaEnvironments
    liftMaybe "getNamespaceRoots" (M.lookup btn nrs)

getEnvRoots             :: Elab m => EnvTypeName -> m [NameRoot]
getEnvRoots stn =
  do
    nrs <- meEnvRoots <$> getMetaEnvironments
    liftMaybe "getEnvRoots" (M.lookup stn nrs)

getNamespaceCtor :: Elab m => NamespaceTypeName -> m (SortTypeName,CtorName)
getNamespaceCtor ntn =
  do
    ctors <- meNamespaceCtor <$> getMetaEnvironments
    liftMaybe "getNamespaceCtor" (M.lookup ntn ctors)

getSortOfNamespace :: Elab m => NamespaceTypeName -> m SortTypeName
getSortOfNamespace ntn = fst <$> getNamespaceCtor ntn

getNamespaceEnvCtor :: Elab m => NamespaceTypeName -> m (EnvTypeName,CtorName)
getNamespaceEnvCtor ntn =
  do
    envCtors <- meNamespaceEnvCtor <$> getMetaEnvironments
    liftMaybe "getNamespaceEnvCtor" (M.lookup ntn envCtors)

getFunctionNames :: Elab m => SortTypeName -> m [FunName]
getFunctionNames stn =
  do
    ftns <- meFunType <$> getMetaEnvironments
    return [ fn
           | (fn, (stn',_)) <- M.toList ftns
           , stn == stn'
           ]

getFunctionType :: Elab m => FunName -> m (SortTypeName,[NamespaceTypeName])
getFunctionType fn =
  do
    ftns <- meFunType <$> getMetaEnvironments
    liftMaybe "getFunctionType" (M.lookup fn ftns)

getShiftRoot :: Elab m => NamespaceTypeName -> m String
getShiftRoot ntn =
  do
    shiftRoots <- meNamespaceShiftRoot <$> getMetaEnvironments
    liftMaybe "getShiftRoot" (M.lookup ntn shiftRoots)

getSubstRoot :: Elab m => NamespaceTypeName -> m String
getSubstRoot ntn =
  do
    substRoots <- meNamespaceSubstRoot <$> getMetaEnvironments
    liftMaybe "getSubstRoot" (M.lookup ntn substRoots)

getNamespaces :: Elab m => m [NamespaceTypeName]
getNamespaces = map fst . M.toList . meNamespaceRoots <$> getMetaEnvironments

getSorts :: Elab m => m [SortTypeName]
getSorts = map fst . M.toList . meSortRoots <$> getMetaEnvironments

getFunctions :: Elab m => m [(FunName,SortTypeName,[NamespaceTypeName])]
getFunctions = do
  ftns <- meFunType <$> getMetaEnvironments
  return [ (fn,stn,ntns) | (fn,(stn,ntns))<- M.toList ftns ]

getEnvironments :: Elab m => m [EnvTypeName]
getEnvironments = map fst . M.toList . meEnvRoots <$> getMetaEnvironments

getRelations :: Elab m => m [RelationTypeName]
getRelations = map fst . M.toList . meRelationRuleNames <$> getMetaEnvironments

hasSingleNamespace :: Elab m => m Bool
hasSingleNamespace = liftM ((==1). length) getNamespaces

getCtorSort :: Elab m => CtorName -> m SortTypeName
getCtorSort cn = do
  ctorSorts <- liftM meCtorSort getMetaEnvironments
  liftMaybe "getCtorSort" (M.lookup cn ctorSorts)

getEnvCtorName :: Elab m => EnvTypeName -> NamespaceTypeName -> m CtorName
getEnvCtorName etn ntn = do
  allCtors <- liftM meEnvCtors getMetaEnvironments
  ctors    <- liftMaybe "getEnvCtorName" (M.lookup etn allCtors)
  case [ cn
       | EnvCtorCons cn mv _ _mbRtn <- ctors
       , typeNameOf mv == ntn
       ] of
    [cn] -> return cn
    []   -> fail "getEnvCtorName: no such constructor"
    _    -> fail "getEnvCtorName: ambiguous namespace"

-- TODO: Allow multiple environment types again.
getEnvCtors :: Elab m => m [CtorName]
getEnvCtors = do
  envCtors <- M.toList . meNamespaceEnvCtor <$> getMetaEnvironments
  return [ cn | (_, (_, cn)) <- envCtors ]

getEnvNamespaceDependencies :: Elab m => EnvTypeName -> m [NamespaceTypeName]
getEnvNamespaceDependencies etn =
  do
    deps <- liftM meEnvNamespaceDeps getMetaEnvironments
    liftMaybe "getEnvNamespaceDependencies" (M.lookup etn deps)

-- TODO: Allow multiple environment types again.
getEnvNamespaces :: Elab m => m [NamespaceTypeName]
getEnvNamespaces = do
  envCtors <- M.toList . meNamespaceEnvCtor <$> getMetaEnvironments
  return [ ntn | (ntn, (_ , _)) <- envCtors ]

getEnvCtorNil :: Elab m => EnvTypeName -> m CtorName
getEnvCtorNil etn = do
  envNil <- meEnvNil <$> getMetaEnvironments
  liftMaybe "getEnvCtorNil" (M.lookup etn envNil)

getEnvCtorConss :: Elab m => EnvTypeName -> m [EnvCtor]
getEnvCtorConss etn = do
  envCtors <- meEnvCtors <$> getMetaEnvironments
  ecs <- liftMaybe "getEnvCtors" (M.lookup etn envCtors)
  return [ ec | ec@EnvCtorCons{} <- ecs ]

--------------------------------------------------------------------------------

class Elab m => ElabRuleM m where
  lookupJudgementOutput :: FunName -> JudgementVariable -> m EnvVariable
  lookupJudgement       :: JudgementVariable -> m (RuleBindSpec, Judgement)

data ElabRuleEnv =
  ElabRuleEnv
  { envJudgementOutput :: Map (FunName, JudgementVariable) EnvVariable
  , envJudgement       :: Map JudgementVariable (RuleBindSpec, Judgement)
  }
  deriving Show

makeElabRuleEnv :: [Formula] -> ElabRuleEnv
makeElabRuleEnv fmls =
  ElabRuleEnv
    (M.fromList
       [ ((fn,jv),ev)
       | FormJudgement jv _rbs _jmt outs <- fmls
       , (fn,ev) <- outs
       ])
    (M.fromList
       [ (jv,(rbs,jmt))
       | FormJudgement jv rbs jmt _outs <- fmls
       ])

newtype ElabRuleT m a = ElabRuleT { fromElabRuleT :: ReaderT ElabRuleEnv m a }
  deriving (Functor, Applicative, Monad, MonadError e, MonadTrans)

deriving instance EnvM m => EnvM (ElabRuleT m)
deriving instance FreshM m => FreshM (ElabRuleT m)
deriving instance Elab m => Elab (ElabRuleT m)

instance (MonadError String m, Elab m) => ElabRuleM (ElabRuleT m) where
  lookupJudgementOutput fn jv = ElabRuleT $ lookupEnv (fn,jv) envJudgementOutput
    "KnotCore.Elaboration.Monad.ElabRuleM(ElabRuleT).lookupJudgementOutput"
  lookupJudgement jv = ElabRuleT $ lookupEnv jv envJudgement
    "KnotCore.Elaboration.Monad.ElabRuleM(ElabRuleT).lookupJudgement"

runElabRuleT :: ElabRuleT m a -> ElabRuleEnv -> m a
runElabRuleT = runReaderT . fromElabRuleT
