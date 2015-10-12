{-# LANGUAGE MultiParamTypeClasses #-}

module KnotCore.Elaboration.Names where

import KnotCore.Syntax
import KnotCore.Elaboration.Monad

--  _  _
-- | \| |__ _ _ __  ___ ___
-- | .` / _` | '  \/ -_|_-<
-- |_|\_\__,_|_|_|_\___/__/

-- Representation of heterogeneous variable lists. This is a list
-- representing a list of variables from all namespaces in the
-- specifications. Unfortunately this is not modular for now.
data HVarlistVar =
  HVLV {
    hvarlistVarRoot       :: NameRoot,
    hvarlistVarSuffix     :: Suffix
  }
  deriving (Eq,Ord,Show)

-- Representation of a cutoff variable. Cutoffs always belong to a
-- single namespace.
data CutoffVar =
  CV {
    cutoffVarRoot      :: NameRoot,
    cutoffVarSuffix    :: Suffix,
    cutoffVarNamespace :: NamespaceTypeName
  }
  deriving (Eq,Ord,Show)

-- Representation of an index variable. Cutoffs always belong to a
-- single namespace.
data IndexVar =
  IndexVar {
    indexVarRoot       :: NameRoot,
    indexVarSuffix     :: Suffix,
    indexVarNamespace  :: NamespaceTypeName,
    indexVarSort       :: SortTypeName
  }
  deriving (Eq,Ord,Show)

toIndex :: Elab m => MetavarVar -> m IndexVar
toIndex (MetavarVar nr suff ntn) = do
  (stn,_) <- getNamespaceCtor ntn
  return $ IndexVar nr suff ntn stn

-- Representation of a trace of a namespace.
data TraceVar =
  TV {
    traceVarRoot       :: NameRoot,
    traceVarSuffix     :: Suffix,
    traceVarNamespace  :: NamespaceTypeName
  }
  deriving (Eq,Ord,Show)

-- -- A homogeneous variable list.
-- data Varlist =
--   Varlist {
--     varlistRoot        :: NameRoot,
--     varlistSuffix      :: Suffix,
--     varlistNamespace   :: NamespaceTypeName
--   }
--   deriving (Eq,Ord,Show)

-- Representation of an term variable.
data TermVar =
  TermVar {
    termVarRoot       :: NameRoot,
    termVarSuffix     :: Suffix,
    termVarSort       :: SortTypeName
  }
  deriving (Eq,Ord,Show)

data Hypothesis =
  Hypothesis {
    hypNameRoot  :: NameRoot,
    hypSuffix    :: Suffix
  }
  deriving (Eq,Ord,Show)

instance TypeNameOf CutoffVar NamespaceTypeName where
  typeNameOf = cutoffVarNamespace
instance TypeNameOf IndexVar NamespaceTypeName where
  typeNameOf = indexVarNamespace
instance TypeNameOf TermVar SortTypeName where
  typeNameOf = termVarSort
instance TypeNameOf TraceVar NamespaceTypeName where
  typeNameOf = traceVarNamespace
instance TypeNameOf EnvVar EnvTypeName where
  typeNameOf = envVarTypeName

class SortOf a where
  sortOf :: a -> SortTypeName

-- instance TypeNameOf a SortTypeName => SortOf a where
--   sortOf = typeNameOf
instance SortOf SubtreeVar where
  sortOf (SubtreeVar _ _ stn) = stn
instance SortOf IndexVar where
  sortOf (IndexVar _ _ _ stn) = stn
