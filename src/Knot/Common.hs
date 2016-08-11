{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}

module Knot.Common
  ( module Knot.Common
  , module Control.Applicative
  , module Data.Monoid
  , module Data.Traversable
  ) where

import           Control.Applicative
import           Control.Monad.Error.Class
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.Except
import           Control.Monad.Trans.Reader
import           Control.Monad.Trans.State.Strict
import           Control.Monad.Trans.Writer.Strict
import           Data.Foldable
import           Data.Function
import           Data.List
import           Data.Monoid
import           Data.Traversable

-- * Snoc lists

infixl 5 :.
data SnocList a = Nil | (:.) (SnocList a) a
  deriving (Functor,Eq,Ord,Traversable,Foldable)

instance Show a => Show (SnocList a) where
  show = show . toList

(.++) :: SnocList a -> SnocList a -> SnocList a
xs .++ Nil       = xs
xs .++ (ys :. y) = (xs .++ ys) :. y

sconcat :: SnocList (SnocList a) -> SnocList a
sconcat Nil         = Nil
sconcat (xss :. xs) = sconcat xss .++ xs

sreverse :: SnocList a -> SnocList a
sreverse = go Nil
  where go a Nil       = a
        go a (xs :. x) = go (a :. x) xs

dropSuffix :: (Applicative m, MonadError String m, Eq a, Show a) =>
  SnocList a -> SnocList a -> m (SnocList a)
dropSuffix xs        Nil       = pure xs
dropSuffix (xs :. x) (ys :. y)
  | x == y    = dropSuffix xs ys
dropSuffix xs        ys       =
  throwError . unwords $
    [ "KnotSpec.DesugarRelations.dropSuffix:"
    , show xs
    , "is not a suffix of"
    , show ys
    ]

dropPrefix :: (Applicative m, MonadError String m, Eq a, Show a) =>
  SnocList a -> SnocList a -> m (SnocList a)
dropPrefix xs ys = sreverse <$> dropSuffix (sreverse ys) (sreverse xs)

-- * Source code locations

data Loc = Loc { line :: !Int, column :: !Int } | LocNoWhere
  deriving (Eq,Ord,Show)

-- * Meta-names

-- | Type for identifiers.
type Identifier = String

-- | Types that are essentially identifiers and can be converted back to
-- 'Identifier'.
class ToId a where
  toIdent :: a -> Identifier

data NamespaceTypeName = NTN   { ntnLoc   :: Loc, ntnId   :: Identifier }
data SortTypeName      = STN   { stnLoc   :: Loc, stnId   :: Identifier }
data EnvTypeName       = ETN   { etnLoc   :: Loc, etnId   :: Identifier }
data RelationTypeName  = RTN   { rtnLoc   :: Loc, rtnId   :: Identifier }
data SetTypeName       = ZTN   { ztnLoc   :: Loc, ztnId   :: Identifier }


data WithMV = WMV | WOMV

data SWithMV :: WithMV -> * where
  SWMV   :: SWithMV 'WMV
  SWOMV  :: SWithMV 'WOMV

data FieldTypeName (w :: WithMV) where
  FieldSortTypeName      :: SortTypeName      -> FieldTypeName w
  FieldSetTypeName       :: SetTypeName       -> FieldTypeName w
  FieldEnvTypeName       :: EnvTypeName       -> FieldTypeName w
  FieldReferenceTypeName :: NamespaceTypeName -> FieldTypeName 'WMV
  FieldBindingTypeName   :: NamespaceTypeName -> FieldTypeName 'WMV

deriving instance Eq (FieldTypeName w)
deriving instance Ord (FieldTypeName w)

instance Show (FieldTypeName w) where
  show (FieldSortTypeName x)      = show x
  show (FieldSetTypeName x)       = show x
  show (FieldEnvTypeName x)       = show x
  show (FieldReferenceTypeName x) = show x
  show (FieldBindingTypeName x)   = show x

data CtorName          = CN    { cnLoc    :: Loc, cnId    :: Identifier }
data FunName           = FN    { fnLoc    :: Loc, fnId    :: Identifier }
data NameRoot          = NR    { nrLoc    :: Loc, nrId    :: Identifier }
type Suffix            = String

data ResolvedTypeName
  = ResNTN NamespaceTypeName
  | ResSTN SortTypeName
  | ResETN EnvTypeName
  | ResRTN RelationTypeName
  | ResZTN SetTypeName
  deriving (Show)

instance ToId ResolvedTypeName where
  toIdent resTn = case resTn of
    ResNTN x -> toIdent x
    ResSTN x -> toIdent x
    ResETN x -> toIdent x
    ResRTN x -> toIdent x
    ResZTN x -> toIdent x


newtype SortGroupTypeName = SGTN { sgtnId :: Identifier } deriving (Eq,Ord)
newtype FunGroupName      = FGN  { fgnId  :: Identifier } deriving (Eq,Ord)

groupName :: [SortTypeName] -> SortGroupTypeName
groupName stns = SGTN (intercalate "_" $ map toIdent stns)

funGroupName :: [FunName] -> FunGroupName
funGroupName fns = FGN (intercalate "_" $ map toIdent fns)

-- ** Meta-variables

data FreeVariable
  = FV
    { fvRoot   :: NameRoot
    , fvSuffix :: Suffix
    , fvNtn    :: NamespaceTypeName
    }
  deriving (Eq,Ord)
data BindingVariable
  = BV
    { bvRoot   :: NameRoot
    , bvSuffix :: Suffix
    , bvNtn    :: NamespaceTypeName
    }
  deriving (Eq,Ord)
data SortVariable
  = SV
    { svRoot   :: NameRoot
    , svSuffix :: Suffix
    , svStn    :: SortTypeName
    }
  deriving (Eq,Ord)
data EnvVariable
  = EV
    { evRoot   :: NameRoot
    , evSuffix :: Suffix
    , evEtn    :: EnvTypeName
    }
  deriving (Eq,Ord)
data JudgementVariable
  = JV
    { jvRoot   :: NameRoot
    , jvSuffix :: Suffix
    , jvRtn    :: RelationTypeName
    }
  deriving (Eq,Ord)
data SetVariable
  = ZV
    { zvRoot   :: NameRoot
    , zvSuffix :: Suffix
    , zvZtn    :: SetTypeName
    }
  deriving (Eq,Ord)

--------------------------------------------------------------------------------

instance Eq NamespaceTypeName where (==) = (==) `on` ntnId
instance Ord NamespaceTypeName where compare = compare `on` ntnId
instance ToId NamespaceTypeName where toIdent = ntnId

instance Eq SortTypeName where (==) = (==) `on` stnId
instance Ord SortTypeName where compare = compare `on` stnId
instance ToId SortTypeName where toIdent = stnId

instance ToId SortGroupTypeName where toIdent = sgtnId

instance Eq EnvTypeName where (==) = (==) `on` etnId
instance Ord EnvTypeName where compare = compare `on` etnId
instance ToId EnvTypeName where toIdent = etnId

instance Eq RelationTypeName where (==) = (==) `on` rtnId
instance Ord RelationTypeName where compare = compare `on` rtnId
instance ToId RelationTypeName where toIdent = rtnId

instance Eq SetTypeName where (==) = (==) `on` ztnId
instance Ord SetTypeName where compare = compare `on` ztnId
instance ToId SetTypeName where toIdent = ztnId

instance Eq NameRoot where (==) = (==) `on` nrId
instance Ord NameRoot where compare = compare `on` nrId
instance ToId NameRoot where toIdent = nrId

instance Eq CtorName where (==) = (==) `on` cnId
instance Ord CtorName where compare = compare `on` cnId
instance ToId CtorName where toIdent = cnId

instance Eq FunName where (==) = (==) `on` fnId
instance Ord FunName where compare = compare `on` fnId
instance ToId FunName where toIdent = fnId

instance ToId (FieldTypeName w) where
  toIdent (FieldSortTypeName stn) = toIdent stn
  toIdent (FieldSetTypeName ztn) = toIdent ztn
  toIdent (FieldEnvTypeName etn) = toIdent etn
  toIdent (FieldReferenceTypeName ntn) = toIdent ntn
  toIdent (FieldBindingTypeName ntn) = toIdent ntn

instance ToId FunGroupName where toIdent = fgnId

instance Show NamespaceTypeName where showsPrec i = showsPrec i . ntnId
instance Show SortTypeName      where showsPrec i = showsPrec i . stnId
instance Show EnvTypeName       where showsPrec i = showsPrec i . etnId
instance Show RelationTypeName  where showsPrec i = showsPrec i . rtnId
instance Show SetTypeName       where showsPrec i = showsPrec i . ztnId
instance Show SortGroupTypeName where showsPrec i = showsPrec i . sgtnId
instance Show FunGroupName      where showsPrec i = showsPrec i . fgnId
instance Show NameRoot          where showsPrec i = showsPrec i . nrId
instance Show CtorName          where showsPrec i = showsPrec i . cnId
instance Show FunName           where showsPrec i = showsPrec i . fnId

showVariable :: ToId t => String -> NameRoot -> Suffix -> Maybe t -> String
showVariable k r s (Just t) = "(" ++ k ++ " " ++ nrId r ++ s ++ " " ++ toIdent t ++ ")"
showVariable k r s Nothing  = "(" ++ k ++ " " ++ nrId r ++ s ++ " " ++ ")"

instance Show FreeVariable      where show (FV r s t)     = showVariable "FV" r s (Just t)
instance Show BindingVariable   where show (BV r s t)     = showVariable "BV" r s (Just t)
instance Show SortVariable      where show (SV r s t)     = showVariable "SV" r s (Just t)
instance Show EnvVariable       where show (EV r s t)     = showVariable "EV" r s (Just t)
instance Show JudgementVariable where show (JV r s t)     = showVariable "JV" r s (Just t)
instance Show SetVariable       where show (ZV r s t)     = showVariable "ZV" r s (Just t)

-- ** Type names

class TypeNameOf a b | a -> b where
  typeNameOf :: a -> b

instance TypeNameOf EnvVariable EnvTypeName where
  typeNameOf = evEtn
instance TypeNameOf SortVariable SortTypeName where
  typeNameOf = svStn
instance TypeNameOf BindingVariable NamespaceTypeName where
  typeNameOf = bvNtn
instance TypeNameOf FreeVariable NamespaceTypeName where
  typeNameOf = fvNtn
instance TypeNameOf JudgementVariable RelationTypeName where
  typeNameOf = jvRtn
instance TypeNameOf SetVariable SetTypeName where
  typeNameOf = zvZtn

--------------------------------------------------------------------------------

data SubstitutableClauseInfo
  = SubstitutableClauseInfo
    { substClauseName         ::  CtorName
    , substClauseRelation     ::  RelationTypeName
    , substClauseVarRule      ::  Maybe CtorName
    , substClauseObligations  ::  [CtorName]
    }
  deriving (Eq,Ord,Show)

--------------------------------------------------------------------------------

class (Applicative m, Monad m) => EnvM m where
  lookupNamespaceSort :: NamespaceTypeName -> m (Maybe SortTypeName)
  lookupFunctionType  :: FunName -> m (SortTypeName, [NamespaceTypeName])
  lookupEnvClause :: EnvTypeName -> NamespaceTypeName -> m ([FieldTypeName 'WOMV], Maybe RelationTypeName)
  lookupRelationType :: RelationTypeName -> m (Maybe EnvTypeName, [FieldTypeName 'WOMV])

  lookupNamespaceRoots :: NamespaceTypeName -> m [NameRoot]
  lookupSortRoots :: SortTypeName -> m [NameRoot]
  lookupEnvRoots :: EnvTypeName -> m [NameRoot]
  lookupRelationRoots :: RelationTypeName -> m [NameRoot]
  lookupSetRoots :: SetTypeName -> m [NameRoot]

  lookupCtorType :: CtorName -> m SortTypeName
  -- lookupRelationOutput :: FunName -> RelationTypeName -> m EnvTypeName

  lookupRelationOutputs :: RelationTypeName -> m [(FunName, EnvTypeName)]
  lookupSortCtors :: SortTypeName -> m [CtorName]
  -- lookupNameRoot     :: NameRoot -> m ResolvedTypeName

instance EnvM m => EnvM (StateT s m) where
  lookupNamespaceSort = lift . lookupNamespaceSort
  lookupFunctionType = lift . lookupFunctionType
  lookupEnvClause = (lift.) . lookupEnvClause
  lookupRelationType = lift . lookupRelationType
  lookupNamespaceRoots = lift . lookupNamespaceRoots
  lookupSortRoots = lift . lookupSortRoots
  lookupEnvRoots = lift . lookupEnvRoots
  lookupRelationRoots = lift . lookupRelationRoots
  lookupSetRoots = lift . lookupSetRoots
  lookupCtorType = lift . lookupCtorType
  -- lookupRelationOutput = (lift.) . lookupRelationOutput
  lookupRelationOutputs = lift . lookupRelationOutputs
  lookupSortCtors = lift . lookupSortCtors
  -- lookupNameRoot = lift . lookupNameRoot
instance EnvM m => EnvM (ReaderT s m) where
  lookupNamespaceSort = lift . lookupNamespaceSort
  lookupFunctionType = lift . lookupFunctionType
  lookupEnvClause = (lift.) . lookupEnvClause
  lookupRelationType = lift . lookupRelationType
  lookupNamespaceRoots = lift . lookupNamespaceRoots
  lookupSortRoots = lift . lookupSortRoots
  lookupEnvRoots = lift . lookupEnvRoots
  lookupRelationRoots = lift . lookupRelationRoots
  lookupSetRoots = lift . lookupSetRoots
  lookupCtorType = lift . lookupCtorType
  -- lookupRelationOutput = (lift.) . lookupRelationOutput
  lookupRelationOutputs = lift . lookupRelationOutputs
  lookupSortCtors = lift . lookupSortCtors
  -- lookupNameRoot = lift . lookupNameRoot
instance (Monoid w, EnvM m) => EnvM (WriterT w m) where
  lookupNamespaceSort = lift . lookupNamespaceSort
  lookupFunctionType = lift . lookupFunctionType
  lookupEnvClause = (lift.) . lookupEnvClause
  lookupRelationType = lift . lookupRelationType
  lookupNamespaceRoots = lift . lookupNamespaceRoots
  lookupSortRoots = lift . lookupSortRoots
  lookupEnvRoots = lift . lookupEnvRoots
  lookupRelationRoots = lift . lookupRelationRoots
  lookupSetRoots = lift . lookupSetRoots
  lookupCtorType = lift . lookupCtorType
  -- lookupRelationOutput = (lift.) . lookupRelationOutput
  lookupRelationOutputs = lift . lookupRelationOutputs
  lookupSortCtors = lift . lookupSortCtors
  -- lookupNameRoot = lift . lookupNameRoot

--------------------------------------------------------------------------------

class (Applicative m, Monad m) => FreshM m where
  freshenSuffix :: NameRoot -> Suffix -> m Suffix
  freshSuffix :: NameRoot -> m Suffix
  freshSuffix nr = freshenSuffix nr ""
  localNames  :: m a -> m a

instance FreshM m => FreshM (StateT s m) where
  freshenSuffix = (lift.) . freshenSuffix
  freshSuffix = lift . freshSuffix
  localNames m = StateT $ localNames . runStateT m

instance FreshM m => FreshM (ReaderT s m) where
  freshenSuffix = (lift.) . freshenSuffix
  freshSuffix = lift . freshSuffix
  localNames m = ReaderT $ localNames . runReaderT m

instance (Monoid w, FreshM m) => FreshM (WriterT w m) where
  freshenSuffix = (lift.) . freshenSuffix
  freshSuffix = lift . freshSuffix
  localNames m = WriterT $ localNames (runWriterT m)

instance (FreshM m) => FreshM (ExceptT e m) where
  freshenSuffix = (lift.) . freshenSuffix
  freshSuffix = lift . freshSuffix
  localNames m = ExceptT $ localNames (runExceptT m)
