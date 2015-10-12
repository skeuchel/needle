{-# LANGUAGE MultiParamTypeClasses #-}

module KnotCore.LookupRelation where

import KnotCore.Syntax

data LookupRelation
  = LookupRelation {
      lkEnvTypeName        ::  EnvTypeName,
      lkCtorName           ::  CtorName,
      lkNamespaceTypeName  ::  NamespaceTypeName,
      lkIndices            ::  [SortTypeName],
      lkHere               ::  LookupHere,
      lkTheres             ::  [LookupThere]
    }
  deriving (Eq,Ord,Show)

data LookupHere
  = LookupHere {
      lhCtorName           ::  CtorName,
      lhVariable           ::  MetavarVar,
      lhFields             ::  [SubtreeVar]
    }
  deriving (Eq,Ord,Show)

data LookupThere
  = LookupThere {
      ltHereCtorName       ::  CtorName,
      ltHereVariable       ::  MetavarVar,
      ltHereIndices        ::  [SubtreeVar],
      ltThereCtorName      ::  CtorName,
      ltThereCtorVariable  ::  MetavarVar,
      ltThereIndices       ::  [SubtreeVar]
    }
  deriving (Eq,Ord,Show)
