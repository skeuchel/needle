{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module KnotCore.LookupRelation where

import KnotCore.Syntax

data LookupRelation
  = LookupRelation
    { lkEnvTypeName        ::  EnvTypeName,
      lkCtorName           ::  CtorName,
      lkNamespaceTypeName  ::  NamespaceTypeName,
      lkIndices            ::  [FieldDecl 'WOMV],
      lkHere               ::  LookupHere,
      lkTheres             ::  [LookupThere]
    }
  deriving (Eq,Ord,Show)

data LookupHere
  = LookupHere
    { lhCtorName           ::  CtorName,
      lhVariable           ::  BindingVariable,
      lhFields             ::  [FieldDecl 'WOMV]
    }
  deriving (Eq,Ord,Show)

data LookupThere
  = LookupThere
    { ltHereCtorName       ::  CtorName,
      ltHereVariable       ::  FreeVariable,
      ltHereIndices        ::  [FieldDecl 'WOMV],
      ltThereCtorName      ::  CtorName,
      ltThereCtorVariable  ::  BindingVariable,
      ltThereIndices       ::  [FieldDecl 'WOMV]
    }
  deriving (Eq,Ord,Show)
