{-# LANGUAGE DeriveFunctor, GeneralizedNewtypeDeriving #-}

module KnotCore.Elaboration.Monad where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Reader (ReaderT(..))
import Control.Monad.Trans.State (StateT(..), evalStateT)
import Control.Monad.Reader.Class
import Control.Monad.State.Class

import Data.List
import Data.Maybe

import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S

import KnotCore.Environment
import KnotCore.Syntax

class (Applicative m, Monad m) => Elab m where
  getMetaEnvironments    :: m MetaEnvironments
  liftMaybe              :: Maybe a -> m a
  freshSuffix            :: NameRoot -> Suffix -> m Suffix
  localNames             :: m a -> m a

newtype ElM a =
  ElM {
    fromElM :: ReaderT MetaEnvironments (StateT (Map String (Set Suffix)) (Either String)) a
  }
  deriving (Functor,Applicative,Monad)

runElM :: ElM a -> MetaEnvironments -> Either String a
runElM (ElM m) env = mm
  where ms = runReaderT m env
        mm = evalStateT ms initialNames

chooseSuffix :: Suffix -> Set Suffix -> Suffix
chooseSuffix suff suffs =
  fromMaybe (error "IMPOSSIBLE") $
    find
      (\s -> not (s `S.member` suffs))
      (suff : map show [0..])

initialNames :: Map String (Set Suffix)
initialNames = M.fromList [("S", S.singleton ""),
                           ("O", S.singleton "")]

instance Elab ElM where
  getMetaEnvironments       = ElM ask
  liftMaybe (Just a)        = return a
  liftMaybe Nothing         = fail "liftMaybe"
  freshSuffix (NR str) suff = ElM $
    do
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
                   sm <- ElM get
                   a <- m
                   ElM (put sm)
                   return a

instance Elab m => Elab (ReaderT r m) where
  getMetaEnvironments = lift getMetaEnvironments
  liftMaybe           = lift . liftMaybe
  freshSuffix nr suff = lift $ freshSuffix nr suff
  localNames m        =
    ReaderT $ \r -> localNames (runReaderT m r)

getSortNamespaceDependencies :: Elab m => SortTypeName -> m [NamespaceTypeName]
getSortNamespaceDependencies stn =
  do
    deps <- meSortNamespaceDeps <$> getMetaEnvironments
    liftMaybe (M.lookup stn deps)

getSortRoots             :: Elab m => SortTypeName -> m [NameRoot]
getSortRoots stn =
  do
    nrs <- meSortRoots <$> getMetaEnvironments
    liftMaybe (M.lookup stn nrs)

getNamespaceRoots :: Elab m => NamespaceTypeName -> m [NameRoot]
getNamespaceRoots btn =
  do
    nrs <- meNamespaceRoots <$> getMetaEnvironments
    liftMaybe (M.lookup btn nrs)

getEnvRoots             :: Elab m => EnvTypeName -> m [NameRoot]
getEnvRoots stn =
  do
    nrs <- meEnvRoots <$> getMetaEnvironments
    liftMaybe (M.lookup stn nrs)

getNamespaceCtor :: Elab m => NamespaceTypeName -> m (SortTypeName,CtorName)
getNamespaceCtor ntn =
  do
    ctors <- meNamespaceCtor <$> getMetaEnvironments
    liftMaybe (M.lookup ntn ctors)

getSortOfNamespace :: Elab m => NamespaceTypeName -> m SortTypeName
getSortOfNamespace ntn = fst <$> getNamespaceCtor ntn

getNamespaceEnvCtor :: Elab m => NamespaceTypeName -> m (EnvTypeName,CtorName)
getNamespaceEnvCtor ntn =
  do
    envCtors <- meNamespaceEnvCtor <$> getMetaEnvironments
    liftMaybe (M.lookup ntn envCtors)

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
    liftMaybe (M.lookup fn ftns)

getShiftRoot :: Elab m => NamespaceTypeName -> m String
getShiftRoot ntn =
  do
    shiftRoots <- meNamespaceShiftRoot <$> getMetaEnvironments
    liftMaybe (M.lookup ntn shiftRoots)

getSubstRoot :: Elab m => NamespaceTypeName -> m String
getSubstRoot ntn =
  do
    substRoots <- meNamespaceSubstRoot <$> getMetaEnvironments
    liftMaybe (M.lookup ntn substRoots)

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

hasSingleNamespace :: Elab m => m Bool
hasSingleNamespace = liftM ((==1). length) getNamespaces

getCtorSort :: Elab m => CtorName -> m SortTypeName
getCtorSort cn = do
  ctorSorts <- liftM meCtorSort getMetaEnvironments
  liftMaybe (M.lookup cn ctorSorts)

getEnvCtorName :: Elab m => EnvTypeName -> NamespaceTypeName -> m CtorName
getEnvCtorName etn ntn = do
  allCtors <- liftM meEnvCtors getMetaEnvironments
  ctors    <- liftMaybe (M.lookup etn allCtors)
  case [ cn
       | EnvCtorCons cn mv _ <- ctors
       , typeNameOf mv == ntn
       ] of
    [cn] -> return cn
    []   -> fail "getEnvCtorName: no such constructor"
    _    -> fail "getEnvCtorName: ambiguous namespace"

getEnvCtors :: Elab m => m [CtorName]
getEnvCtors = do
  envCtors <- M.toList . meNamespaceEnvCtor <$> getMetaEnvironments
  return [ cn | (_, (_, cn)) <- envCtors ]

getEnvNamespaceDependencies :: Elab m => EnvTypeName -> m [NamespaceTypeName]
getEnvNamespaceDependencies etn =
  do
    deps <- liftM meEnvNamespaceDeps getMetaEnvironments
    liftMaybe (M.lookup etn deps)
