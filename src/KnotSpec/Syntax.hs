{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_HADDOCK show-extensions #-}

{-|
Module      : KnotSpec.Syntax
Description : Abstract syntax tree types for the KnotSpec frontend
Copyright   : (c) Steven Keuchel, 2016
License     : BSD-3-Clause
Maintainer  : steven.keuchel@gmail.com
Stability   : experimental
Portability : non-portable (GHC extensions)

This module contains the definition of the abstract syntax trees for the
frontend of needle. The frontend goes through multiple phases before being
converted to the 'KnotCore' representation. We use the promoted version of
'Phase' to index the AST by the phase and change the AST slightly depending on
the phase. In essence we have a different AST per phase but can combine them
with some type level trickery to avoid duplication.
-}

module KnotSpec.Syntax
  ( module Knot.Common
  , module KnotSpec.Syntax
  )
  where

import           Knot.Common

import           Control.Applicative
import           Control.Monad
import           Control.Monad.Error.Class
import           Data.Function
import           Data.Monoid
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Traversable

-- * Phases

-- | Phase state datatype
data Phase
  -- | The 'Parsed' phase is the target AST of the parser before any kind of
  -- analysis.
  = Parsed
  -- | Name resolution is the first phase after parsing and transitions the AST
  -- from the 'Parsed' state to the 'Resolved' state. All identifiers for
  -- typenames have been resolved to namespace, sort or environment typenames
  -- and variables have been resolved to meta, sort or environment
  -- variables. Additionally, this is also where we distinguish between
  -- referencing and binding occurrences of meta-variables.
  | ResolvedTypes
  | ResolvedVars
  -- | During type-checking we annotate the AST with additional information
  -- which is available in the 'Checked' state.
  | Checked
  -- | After type-checking we analyze the recursive structure of the
  -- specification and group mutually-recursive sets of sorts and functions.
  | Grouped

data SPhase :: Phase -> * where
  SParsed            :: SPhase 'Parsed
  SResolvedTypes     :: SPhase 'ResolvedTypes
  SResolvedVars      :: SPhase 'ResolvedVars
  SChecked           :: SPhase 'Checked
  SGrouped           :: SPhase 'Grouped

class SPhaseC p where
  sphase :: SPhase p
instance SPhaseC 'Parsed where
  sphase = SParsed
instance SPhaseC 'ResolvedTypes where
  sphase = SResolvedTypes
instance SPhaseC 'ResolvedVars where
  sphase = SResolvedVars
instance SPhaseC 'Checked where
  sphase = SChecked
instance SPhaseC 'Grouped where
  sphase = SGrouped

class SWithMVC w where
  sWithMV :: SWithMV w
instance SWithMVC 'WMV where
  sWithMV = SWMV
instance SWithMVC 'WOMV where
  sWithMV = SWOMV

type family IsTypeResolvedF (p :: Phase) :: Bool where
  IsTypeResolvedF 'Parsed        = 'False
  IsTypeResolvedF 'ResolvedTypes = 'True
  IsTypeResolvedF 'ResolvedVars  = 'True
  IsTypeResolvedF 'Checked       = 'True
  IsTypeResolvedF 'Grouped       = 'True

type family IsVarResolvedF (p :: Phase) :: Bool where
  IsVarResolvedF 'Parsed         = 'False
  IsVarResolvedF 'ResolvedTypes  = 'False
  IsVarResolvedF 'ResolvedVars   = 'True
  IsVarResolvedF 'Checked        = 'True
  IsVarResolvedF 'Grouped        = 'True

type family IsGroupedF (p :: Phase) :: Bool where
  IsGroupedF 'Parsed             = 'False
  IsGroupedF 'ResolvedTypes      = 'False
  IsGroupedF 'ResolvedVars       = 'False
  IsGroupedF 'Checked            = 'False
  IsGroupedF 'Grouped            = 'True

type IsTypeResolved p = IsTypeResolvedF p ~ 'True
type IsVarResolved p = IsVarResolvedF p ~ 'True
type IsGrouped p = IsGroupedF p ~ 'True

-- type IsNotTypeResolved p = IsTypeResolvedF p ~ False
type IsNotVarResolved p = IsVarResolvedF p ~ 'False
type IsNotGrouped p = IsGroupedF p ~ 'False

type TypeResolved p =
  ( SPhaseC p
  , IsTypeResolved p
  , PhNamespaceTypeName p ~ NamespaceTypeName
  , PhEnvTypeName p ~ EnvTypeName
  , PhSortTypeName p ~ SortTypeName
  , PhSetTypeName p ~ SetTypeName
  , PhFieldTypeName 'WMV p ~ FieldTypeName 'WMV
  , PhFieldTypeName 'WOMV p ~ FieldTypeName 'WOMV
  , PhRelationTypeName p ~ RelationTypeName
  , PhRawTypeName p ~ ResolvedTypeName
  )

type VarResolved p =
  ( TypeResolved p
  , IsVarResolved p
  , PhSortVariable p ~ SortVariable
  , PhEnvVariable p ~ EnvVariable
  , PhSetVariable p ~ SetVariable
  , PhBindingVariable p ~ BindingVariable
  , PhFreeVariable p ~ FreeVariable
  , PhRuleMetavarBinders p ~ [RuleMetavarBinder p]
  )

-- * Metanames

data RawTypeName = RawTN { rawTnLoc :: Loc, rawTnId :: Identifier }

rawToNamespaceTypeName :: RawTypeName -> NamespaceTypeName
rawToNamespaceTypeName (RawTN loc ident) = NTN loc ident

rawToSortTypeName :: RawTypeName -> SortTypeName
rawToSortTypeName (RawTN loc ident) = STN loc ident

rawToEnvTypeName :: RawTypeName -> EnvTypeName
rawToEnvTypeName (RawTN loc ident) = ETN loc ident

rawToRelationTypeName :: RawTypeName -> RelationTypeName
rawToRelationTypeName (RawTN loc ident) = RTN loc ident

rawToSetTypeName :: RawTypeName -> SetTypeName
rawToSetTypeName (RawTN loc ident) = ZTN loc ident

-- ** Variables

-- | An unresolved variable. This type should only be used in the 'Parsed'
-- or 'ResolvedTypes' states.

data RawVariable (p :: Phase)
  = (p ~ 'Parsed) =>
    RawVarParsed
    { rawRoot       :: NameRoot
    , rawSuffix     :: Suffix
    , rawTypeNameMb :: Maybe (PhRawTypeName p)
    }
  | (IsTypeResolved p) =>
    RawVar
    { rawRoot       :: NameRoot
    , rawSuffix     :: Suffix
    , rawTypeName   :: PhRawTypeName p
    }

type family PhRawTypeName (p :: Phase) where
  PhRawTypeName 'Parsed = RawTypeName
  PhRawTypeName p = ResolvedTypeName

data ResolvedVariable
  = ResBV BindingVariable
  | ResFV FreeVariable
  | ResSV SortVariable
  | ResEV EnvVariable
  | ResJV JudgementVariable
  | ResZV SetVariable
  deriving (Show)

type family PhFreeVariable (p :: Phase) where
  PhFreeVariable 'Parsed                  = RawVariable 'Parsed
  PhFreeVariable 'ResolvedTypes           = RawVariable 'ResolvedTypes
  PhFreeVariable a                        = FreeVariable
type family PhBindingVariable (p :: Phase) where
  PhBindingVariable 'Parsed               = RawVariable 'Parsed
  PhBindingVariable 'ResolvedTypes        = RawVariable 'ResolvedTypes
  PhBindingVariable a                     = BindingVariable
type family PhSortVariable (p :: Phase) where
  PhSortVariable 'Parsed                  = RawVariable 'Parsed
  PhSortVariable 'ResolvedTypes           = RawVariable 'ResolvedTypes
  PhSortVariable a                        = SortVariable
type family PhEnvVariable (p :: Phase) where
  PhEnvVariable 'Parsed                   = RawVariable 'Parsed
  PhEnvVariable 'ResolvedTypes            = RawVariable 'ResolvedTypes
  PhEnvVariable a                         = EnvVariable
type family PhJudgementVariable (p :: Phase) where
  PhJudgementVariable 'Parsed             = RawVariable 'Parsed
  PhJudgementVariable 'ResolvedTypes      = RawVariable 'ResolvedTypes
  PhJudgementVariable a                   = JudgementVariable
type family PhMaybeJudgementVariable (p :: Phase) where
  PhMaybeJudgementVariable 'Parsed        = Maybe (RawVariable 'Parsed)
  PhMaybeJudgementVariable 'ResolvedTypes = Maybe (RawVariable 'ResolvedTypes)
  PhMaybeJudgementVariable a              = JudgementVariable
type family PhSetVariable (p :: Phase) where
  PhSetVariable 'Parsed                   = RawVariable 'Parsed
  PhSetVariable 'ResolvedTypes            = RawVariable 'ResolvedTypes
  PhSetVariable a                         = SetVariable

-- * Specification

-- | A complete Knot specification
data TermSpec (p :: Phase)
  = IsNotVarResolved p =>
    TermSpecRaw
    { tsDecls :: [Decl p]
    }
  | (IsVarResolved p, IsNotGrouped p) =>
    TermSpec
    { tsNamespaceDecls          ::  [NamespaceDecl p]
    , tsSortDecls               ::  [SortDecl p]
    , tsEnvDecls                ::  [EnvDecl p]
    , tsFunDecls                ::  [FunDecl p]
    , tsRelationDecls           ::  [RelationDecl p]
    , tsSetDecls                ::  [SetDecl p]
    }
  | (IsVarResolved p, IsGrouped p) =>
    TermSpecGrouped
    { tsNamespaceDecls          ::  [NamespaceDecl p]
    , tsSortGroupDecls          ::  [SortGroupDecl p]
    , tsEnvDecls                ::  [EnvDecl p]
    , tsFunGroupDecls           ::  [FunGroupDecl p]
    , tsRelationGroupDecls      ::  [RelationGroupDecl p]
    , tsSetGroupDecls           ::  [SetGroupDecl p]
    }

data Decl p
  = ND (NamespaceDecl p)
  | SD (SortDecl p)
  | FD (FunDecl p)
  | ED (EnvDecl p)
  | RD (RelationDecl p)
  | ZD (SetDecl p)

-- * Namespaces

-- | The type used for namespace type names depending on the phase state.
type family PhNamespaceTypeName (p :: Phase) where
  PhNamespaceTypeName 'Parsed = RawTypeName
  PhNamespaceTypeName a       = NamespaceTypeName

data NamespaceDecl (p :: Phase)
  = NamespaceDecl
    { ndLocStart                ::  Loc
    , ndTypeName                ::  PhNamespaceTypeName p
    , ndNameRoots               ::  [NameRoot]
    , ndSort                    ::  Maybe (PhSortTypeName p)
    , ndDirectives              ::  [NamespaceDirective]
    , ndLocEnd                  ::  Loc
    }

data NamespaceDirective
  = NamespaceShift String
  | NamespaceSubst String
  | NamespaceWeaken String
  | NamespaceCutoff String
  deriving Show

-- * Sorts

data SortGroupDecl (p :: Phase)
  = IsGrouped p =>
    SortGroupDecl
    { sgdTypeName               ::  SortGroupTypeName
    , sgdSorts                  ::  [SortDecl p]
    , sgdNamespaces             ::  [NamespaceTypeName]
    , sgdHasBindSpec            ::  Bool
    }

-- | The type used for sort type names depending on the phase state.
type family PhSortTypeName (p :: Phase) where
  PhSortTypeName 'Parsed = RawTypeName
  PhSortTypeName a      = SortTypeName

type family PhFieldTypeName w (p :: Phase) where
  PhFieldTypeName w 'Parsed = RawTypeName
  PhFieldTypeName w a       = FieldTypeName w

data SortDecl (p :: Phase)
  = SortDecl
    { sdTypeName                ::  PhSortTypeName p
    , sdNameRoots               ::  [NameRoot]
    , sdCtors                   ::  [CtorDecl p]
    }

data CtorDecl (p :: Phase)
  = CtorVar
    { ctorDeclName              ::  CtorName
    , ctorDeclReference         ::  PhFreeVariable p
    }
  | CtorReg
    { ctorDeclName              ::  CtorName
    , ctorDeclFields            ::  [FieldDecl 'WMV p p]
    }

data FieldDecl (w :: WithMV) (p :: Phase) (q :: Phase)
  = IsNotVarResolved q =>
    FieldDeclRaw
    { fieldDeclLoc              ::  Loc
    , fieldDeclBindSpec         ::  BindSpec p
    , fieldDeclRawVariable      ::  RawVariable q
    }
  | IsVarResolved q =>
    FieldDeclSort
    { fieldDeclLoc              ::  Loc
    , fieldDeclBindSpec         ::  BindSpec p
    , fieldDeclSortVariable     ::  PhSortVariable q
    }
  | IsVarResolved q =>
    FieldDeclEnv
    { fieldDeclLoc              ::  Loc
    , fieldDeclBindSpec         ::  BindSpec p
    , fieldDeclEnvVariable      ::  PhEnvVariable q
    }
  | (IsVarResolved q, w ~ 'WMV) =>
    FieldDeclBinding
    { fieldDeclLoc              ::  Loc
    , fieldDeclBindSpecInf      ::  PhBindSpecInf p
    , fieldDeclBindingVariable  ::  PhBindingVariable q
    }
  | (w ~ 'WMV) =>
    FieldDeclReference
    { fieldDeclLoc              ::  Loc
    , fieldDeclFreeVariable     ::  PhFreeVariable q
    }
  | IsVarResolved q =>
    FieldDeclSet
    { fieldDeclLoc              ::  Loc
    , fieldDeclSetVariable      ::  PhSetVariable q
    }

-- * Binding specifications

type BindSpec p = SnocList (BindSpecItem p)
data BindSpecItem (p :: Phase)
  = BsiBinding
    { bsiBindingVariable        ::  PhBindingVariable p
    }
  | BsiCall
    { bsiFunName                ::  FunName
    , bsiField                  ::  PhSortVariable p
    }

-- | Binding specification unification variables are used during scope inference
-- of metavariables.
newtype BindSpecVar = BSV { fromBSV :: Integer }
  deriving (Show,Eq,Ord)

-- | BindSpecItems are annotated with their respective outer scope. This
-- information is inferred during the type-checking phase.
type family PhBindSpecInf (p :: Phase) where
  PhBindSpecInf 'Parsed        = ()
  PhBindSpecInf 'ResolvedTypes = ()
  PhBindSpecInf 'ResolvedVars  = ()
  PhBindSpecInf 'Checked       = BindSpec 'Checked
  PhBindSpecInf 'Grouped       = BindSpec 'Grouped

-- * Sets

data SetGroupDecl (p :: Phase)
  = IsGrouped p =>
    SetGroupDecl
    { zgdSets                   ::  [SetDecl p]
    }

-- | The type used for set type names depending on the phase state.
type family PhSetTypeName (p :: Phase) where
  PhSetTypeName 'Parsed = RawTypeName
  PhSetTypeName a       = SetTypeName

data SetDecl (p :: Phase)
  = SetDecl
    { zdTypeName                ::  PhSetTypeName p
    , zdNameRoots               ::  [NameRoot]
    , zdCtors                   ::  [SetCtorDecl p]
    }

data SetCtorDecl (p :: Phase)
  = SetCtor
    { setCtorName               ::  CtorName
    , setCtorFields             ::  [SetFieldDecl p]
    }

data SetFieldDecl (p :: Phase)
  = SetFieldDecl
    { setFieldDeclLoc           ::  Loc
    , setFieldDeclSetVariable   ::  PhSetVariable p
    }

instance (TypeNameOf (PhSetVariable p) SetTypeName) =>
  TypeNameOf (SetFieldDecl p) SetTypeName where
  typeNameOf = typeNameOf . setFieldDeclSetVariable
--  ___             _   _
-- | __|  _ _ _  __| |_(_)___ _ _  ___
-- | _| || | ' \/ _|  _| / _ \ ' \(_-<
-- |_| \_,_|_||_\__|\__|_\___/_||_/__/

data FunGroupDecl (p :: Phase)
  = IsGrouped p =>
    FunGroupDecl
    { fgdTypeName               ::  FunGroupName
    , fgdSortGroup              ::  SortGroupTypeName
    , fgdFunDecls               ::  [(SortTypeName, [FunDecl p])]
    }

data FunDecl (p :: Phase)
  = FunDecl
    { fdName                    ::  FunName
    , fdSource                  ::  PhSortTypeName p
    , fdTarget                  ::  [PhNamespaceTypeName p]
    , fdCases                   ::  [FunCase p]
    }

data FunCase (p :: Phase)
  = FunCase
    { fcCtor                    ::  CtorName
    , fcFields                  ::  [FunField p]
    , fcRhs                     ::  BindSpec p
    }

data FunField (p :: Phase)
  = IsNotVarResolved p =>
    FunFieldRaw
    { ffVariable                ::  RawVariable p
    }
  | IsVarResolved p =>
    FunFieldSort
    { ffSortVariable            ::  PhSortVariable p
    }
  | IsVarResolved p =>
    FunFieldBinding
    { ffBindingVariable         ::  PhBindingVariable p
    }
  | IsVarResolved p =>
    FunFieldEnv
    { ffEnvVariable             ::  PhEnvVariable p
    }
  | IsVarResolved p =>
    FunFieldSet
    { ffSetVariable             ::  PhSetVariable p
    }
  | FunFieldReference
    { ffFreeVariable            ::  PhFreeVariable p
    }

-- * Environments

-- | The type used for environments type names depending on the phase state.
type family PhEnvTypeName (p :: Phase) where
  PhEnvTypeName 'Parsed = RawTypeName
  PhEnvTypeName a      = EnvTypeName

data EnvDecl (p :: Phase)
  = EnvDecl
    { edTypeName                ::  PhEnvTypeName p
    , edNameRoots               ::  [NameRoot]
    , edCtors                   ::  [EnvCtorDecl p]
    }

data EnvCtorDecl (p :: Phase)
  = EnvCtorNil
    { envCtorName               ::  CtorName
    }
  | EnvCtorCons
    { envCtorName               ::  CtorName
    , envCtorBindingVariable    ::  PhBindingVariable p
    , envCtorFields             ::  [FieldDecl 'WOMV p p]
    , envCtorHypo               ::  Maybe (PhRelationTypeName p)
    }

-- * Relations

data RelationGroupDecl (p :: Phase)
  = IsGrouped p =>
    RelationGroupDecl
    { rgdRelations              ::  [RelationDecl p]
    }

-- | Representation for relation declarations.
type family PhRelationTypeName (p :: Phase) where
  PhRelationTypeName 'Parsed = RawTypeName
  PhRelationTypeName a      = RelationTypeName

data RelationDecl (p :: Phase)
  = RelationDecl
    { rdEnv                     ::  Maybe (PhEnvTypeName p)
    , rdTypeName                ::  PhRelationTypeName p
    , rdIndices                 ::  [FieldDecl 'WOMV p p]
    , rdNameRoots               ::  [NameRoot]
    , rdOutputs                 ::  [(FunName, PhEnvTypeName p)]
    , rdRules                   ::  [Rule p]
    }

data RuleMetavarBinder (p :: Phase)
  = RuleMetavarSort
    { rmbBindspecInf            ::  PhBindSpecInf p,
      rmbSortVariable           ::  PhSortVariable p
    }
  | RuleMetavarBinding
    { rmbBindspecInf            ::  PhBindSpecInf p,
      rmbBindingVariable        ::  PhBindingVariable p
    }
  | RuleMetavarFree
    { rmbFreeVariable           ::  PhFreeVariable p
    }
  | RuleMetavarSet
    { rmbSetVariable            ::  PhSetVariable p
    }

type family PhRuleMetavarBinders (p :: Phase) where
  PhRuleMetavarBinders 'Parsed        = ()
  PhRuleMetavarBinders 'ResolvedTypes = ()
  PhRuleMetavarBinders p              = [RuleMetavarBinder p]

data Rule (p :: Phase)
  = RuleVar
    { ruleName                  ::  CtorName
    , ruleMetavarBinders        ::  PhRuleMetavarBinders p
    , ruleVarEnvTypeName        ::  PhLookupEnvTypeName p
    , ruleVarFreeVariable       ::  PhFreeVariable p
    , ruleVarData               ::  [SymbolicField 'WOMV p]
    , ruleConclusion            ::  Judgement p
    }
  | RuleReg
    { ruleName                  ::  CtorName
    , ruleMetavarBinders        ::  PhRuleMetavarBinders p
    , rulePremises              ::  [Formula p]
    , ruleConclusion            ::  Judgement p
    , ruleOutputs               ::  [(FunName, RuleBindSpec p)]
    }

type family PhLookupEnvTypeName (p :: Phase) where
  PhLookupEnvTypeName 'Parsed              = ()
  PhLookupEnvTypeName p                    = EnvTypeName

type family PhFormJudgementOutputs (p :: Phase) where
  PhFormJudgementOutputs 'Parsed        = ()
  PhFormJudgementOutputs 'ResolvedTypes = ()
  PhFormJudgementOutputs p              = [(FunName, EnvVariable)]

data Formula (p :: Phase)
  = FormLookup
    { fmlLookupEnvTypeName      ::  PhLookupEnvTypeName p
    , fmlLookupFreeVariable     ::  PhFreeVariable p
    , fmlLookupData             ::  [SymbolicField 'WOMV p]
    }
  | FormJudgement
    { fmlJmtMaybeVariable       ::  PhMaybeJudgementVariable p
    , fmlJmtRuleBindSpec        ::  RuleBindSpec p
    , fmlJmtJudgement           ::  Judgement p
    , fmtJmtOutputs             ::  PhFormJudgementOutputs p
    }

type family PhJudgementEnvTypeName (p :: Phase) where
  PhJudgementEnvTypeName 'Parsed        = ()
  PhJudgementEnvTypeName 'ResolvedTypes = ()
  PhJudgementEnvTypeName 'ResolvedVars  = ()
  PhJudgementEnvTypeName p             = Maybe EnvTypeName

data Judgement (p :: Phase)
  = Judgement
    { jmtRelationTypeName       ::  PhRelationTypeName p
    , jmtEnvTypeName            ::  PhJudgementEnvTypeName p
    , jmtTerms                  ::  [SymbolicField 'WOMV p]
    }

type RuleBindSpec p = SnocList (RuleBindSpecItem p)
data RuleBindSpecItem (p :: Phase)
  = RuleBsiBinding
    { rbsiBindingVariable       ::  PhBindingVariable p
    , rbsiTerms                 ::  [SymbolicField 'WOMV p]
    }
  | RuleBsiCall
    { rbsiFunName               ::  FunName
    , rbsiJudgement             ::  PhJudgementVariable p
    }

-- | Symbolic term representation

data SymbolicTerm (p :: Phase)
  = IsNotVarResolved p =>
    SymCtorVarRaw
    { stCtorName                ::  CtorName
    , stCtorVarRawVariable      ::  RawVariable p
    }
  | SymVar
    { stScope                   ::  PhBindSpecInf p
    , stSortVar                 ::  PhSortVariable p
    }
  | IsVarResolved p =>
    SymCtorVarFree
    { stScope                   ::  PhBindSpecInf p
    , stCtorName                ::  CtorName
    , stFreeVariable            ::  PhFreeVariable p
    }
  | IsVarResolved p =>
    SymCtorVarBound
    { stScope                   ::  PhBindSpecInf p
    , stCtorName                ::  CtorName
    , stBindingVariable         ::  PhBindingVariable p
    -- , stBindSpecBinding         ::  PhBindSpecInf p      -- Scope where the BV was introduced
    }
  | IsNotVarResolved p =>
    SymCtorRegRaw
    { stCtorName                ::  CtorName
    , stFields                  ::  [SymbolicField 'WMV p]
    }
  | IsVarResolved p =>
    SymCtorReg
    { stScope                   ::  PhBindSpecInf p
    , stCtorName                ::  CtorName
    , stFields                  ::  [SymbolicField 'WMV p]
    }
  | SymWeaken
    { stScope                   ::  PhBindSpecInf p
    , stWeakenInnerScope        ::  PhBindSpecInf p
    , stWeakenTerm              ::  SymbolicTerm p
    , stWeakenDiff              ::  BindSpec p
    }
  | SymSubst
    { stScope                   ::  PhBindSpecInf p
    , stSubstBindingVariable    ::  PhBindingVariable p
    , stSubstitute              ::  SymbolicTerm p
    , stSubstitutee             ::  SymbolicTerm p
    }

data SymbolicField (w :: WithMV) (p :: Phase)
  = IsNotVarResolved p =>
    SymFieldRawVar
    { symFieldLoc               ::  Loc
    , symFieldName              ::  RawVariable p
    }
  | IsNotVarResolved p =>
    SymFieldRawTerm
    { symFieldLoc               ::  Loc
    , symFieldSymbolicTerm      ::  SymbolicTerm p
    }
  | IsVarResolved p =>
    SymFieldSort
    { symFieldLoc               ::  Loc
    , symFieldScope             ::  PhBindSpecInf p
    , symFieldSymbolicTerm      ::  SymbolicTerm p
    }
  | IsVarResolved p =>
    SymFieldEnv
    { symFieldLoc               ::  Loc
    , symFieldScope             ::  PhBindSpecInf p
    , symFieldSymbolicEnv       ::  SymbolicEnv p
    }
  | (IsVarResolved p, w ~ 'WMV) =>
    SymFieldBinding
    { symFieldLoc               ::  Loc
    , symFieldScope             ::  PhBindSpecInf p  -- Scope of this node
    , symFieldBindingVariable   ::  BindingVariable
    }
  | (IsVarResolved p, w ~ 'WMV) =>
    SymFieldReferenceFree
    { symFieldLoc               ::  Loc
    , symFieldScope             ::  PhBindSpecInf p
    , symFieldReferenceVariable ::  FreeVariable
    }
  | (IsVarResolved p, w ~ 'WMV) =>
    SymFieldReferenceBound
    { symFieldLoc               ::  Loc
    , symFieldScope             ::  PhBindSpecInf p
    , symFieldBindingVariable   ::  BindingVariable
    }
  | IsVarResolved p =>
    SymFieldSet
    { symFieldLoc               ::  Loc
    , symFieldScope             ::  PhBindSpecInf p
    , symFieldSymbolicSet       ::  SymbolicSet p
    }

data SymbolicEnv (p :: Phase)
  = IsVarResolved p =>
    SymEnvVar
    { seScope                   ::  PhBindSpecInf p
    , seEnvVar                  ::  EnvVariable
    }
  | IsVarResolved p =>
    SymEnvNil
    { seScope                   ::  PhBindSpecInf p
    , seEnvTypeName             ::  EnvTypeName
    }
  | IsVarResolved p =>
    SymEnvCons
    { seScope                   ::  PhBindSpecInf p
    , seTail                    ::  SymbolicEnv p
    , seCtor                    ::  CtorName
    , seNamespace               ::  NamespaceTypeName
    , seIndices                 ::  [SymbolicField 'WOMV p]
    }

data SymbolicSet (p :: Phase)
  = IsVarResolved p =>
    SymSetVar
    { ssSetVar                  ::  SetVariable
    }
  | IsVarResolved p =>
    SymSetCtor
    { ssCtorName                ::  CtorName
    , ssFields                  ::  [SymbolicSet p]
    }

--------------------------------------------------------------------------------

instance (PhSortTypeName p ~ stn) => TypeNameOf (SortDecl p) stn where
  typeNameOf = sdTypeName

instance (PhSetTypeName p ~ stn) => TypeNameOf (SetDecl p) stn where
  typeNameOf = zdTypeName

data EitherC c1 c2 = c1 => LeftC | c2 => RightC

checkP :: TypeResolved p => SPhase p -> EitherC (p ~ 'ResolvedTypes) (VarResolved p)
checkP sp = case sp of
  SResolvedTypes -> LeftC
  SResolvedVars  -> RightC
  SChecked       -> RightC
  SGrouped       -> RightC

instance (TypeResolved q, SWithMVC w) =>
  TypeNameOf (FieldDecl w p q) (FieldTypeName w)  where
 typeNameOf fd = case checkP (sphase :: SPhase q)  of
   LeftC -> case fd of
     FieldDeclReference{fieldDeclFreeVariable = fv} ->
       case typeNameOf fv of
         ResNTN ntn -> FieldReferenceTypeName ntn
         _          -> error "IMPOSSIBLE"
     FieldDeclRaw{fieldDeclRawVariable = rawVar} ->
       case typeNameOf rawVar of
         ResNTN ntn -> case sWithMV :: SWithMV w of
                         SWMV -> FieldBindingTypeName ntn
                         SWOMV -> error "IMPOSSIBLE"
         ResSTN stn -> FieldSortTypeName stn
         ResETN etn -> FieldEnvTypeName etn
         ResZTN ztn -> FieldSetTypeName ztn
         ResRTN _rtn -> error "IMPOSSIBLE"

   RightC -> case fd of
     FieldDeclSort{fieldDeclSortVariable = sv} ->
       FieldSortTypeName (typeNameOf sv)
     FieldDeclEnv{fieldDeclEnvVariable = ev} ->
       FieldEnvTypeName (typeNameOf ev)
     FieldDeclBinding{fieldDeclBindingVariable = bv} ->
       FieldBindingTypeName (typeNameOf bv)
     FieldDeclReference{fieldDeclFreeVariable = fv} ->
       FieldReferenceTypeName (typeNameOf fv)
     FieldDeclSet{fieldDeclSetVariable = zv} ->
       FieldSetTypeName (typeNameOf zv)

--------------------------------------------------------------------------------

instance Eq RawTypeName where (==) = (==) `on` rawTnId
instance Ord RawTypeName where compare = compare `on` rawTnId
instance ToId RawTypeName where toIdent = rawTnId

instance ToId (RawVariable p) where
  toIdent (RawVarParsed nr s _) = toIdent nr <> s
  toIdent (RawVar nr s _) = toIdent nr <> s
instance Eq (RawVariable p) where (==) = (==) `on` toIdent
instance Ord (RawVariable p) where compare = compare `on` toIdent

instance Show RawTypeName       where show             = show . rawTnId

instance ToId (PhRawTypeName p) => Show (RawVariable p) where
  show (RawVarParsed r s t)  = showVariable "Raw" r s t
  show (RawVar r s t)        = showVariable "Raw" r s (Just t)

instance TypeNameOf (RawVariable 'ResolvedTypes) ResolvedTypeName where
  typeNameOf = rawTypeName

class ToRaw a b | a -> b where
  toRaw :: a -> b

instance ToRaw NamespaceTypeName RawTypeName where
  toRaw (NTN loc ident) = RawTN loc ident
instance ToRaw SortTypeName RawTypeName where
  toRaw (STN loc ident) = RawTN loc ident
instance ToRaw EnvTypeName RawTypeName where
  toRaw (ETN loc ident) = RawTN loc ident
instance ToRaw SetTypeName RawTypeName where
  toRaw (ZTN loc ident) = RawTN loc ident
instance ToRaw RelationTypeName RawTypeName where
  toRaw (RTN loc ident) = RawTN loc ident

instance ToRaw FreeVariable (RawVariable 'ResolvedTypes) where
   toRaw (FV r s t) = RawVar r s (ResNTN t)
instance ToRaw BindingVariable (RawVariable 'ResolvedTypes) where
  toRaw (BV r s t) = RawVar r s (ResNTN t)
instance ToRaw SortVariable (RawVariable 'ResolvedTypes) where
  toRaw (SV r s t) = RawVar r s (ResSTN t)
instance ToRaw EnvVariable (RawVariable 'ResolvedTypes) where
  toRaw (EV r s t) = RawVar r s (ResETN t)
instance ToRaw SetVariable (RawVariable 'ResolvedTypes) where
  toRaw (ZV r s t) = RawVar r s (ResZTN t)

--------------------------------------------------------------------------------

type ShowQ p =
  ( Show (PhBindSpecInf p)
  , Show (PhBindingVariable p)
  , Show (PhEnvTypeName p)
  , Show (PhEnvVariable p)
  , Show (PhFreeVariable p)
  , Show (PhJudgementEnvTypeName p)
  , Show (PhJudgementVariable p)
  , Show (PhLookupEnvTypeName p)
  , Show (PhMaybeJudgementVariable p)
  , Show (PhNamespaceTypeName p)
  , Show (PhRawTypeName p)
  , Show (PhRelationTypeName p)
  , Show (PhRuleMetavarBinders p)
  , Show (PhSetTypeName p)
  , Show (PhSetVariable p)
  , Show (PhSortTypeName p)
  , Show (PhSortVariable p)
  , ToId (PhRawTypeName p)
  )

deriving instance
  ( ShowQ p
  , Show (PhFieldTypeName 'WOMV p)
  , Show (PhFormJudgementOutputs p)
  ) => Show (TermSpec p)

deriving instance
  ( ShowQ p
  , Show (PhFieldTypeName 'WOMV p)
  , Show (PhFormJudgementOutputs p)
  , Show (PhBindSpecInf p)
  ) => Show (Decl p)

deriving instance
  ( ShowQ p
  ) => Show (NamespaceDecl p)

deriving instance
  ( ShowQ p
  ) => Show (SortGroupDecl p)

deriving instance
  ( ShowQ p
  ) => Show (SortDecl p)

deriving instance
  ( ShowQ p
  ) => Show (CtorDecl p)

deriving instance
  ( ShowQ p
  ) => Show (FieldDecl w p p)

deriving instance
  ( ShowQ p
  , Eq (PhSortVariable p)
  , Eq (PhBindingVariable p)
  ) => Eq (BindSpecItem p)

deriving instance
  ( ShowQ p
  ) => Show (BindSpecItem p)

deriving instance
  ( ShowQ p
  ) => Show (FunGroupDecl p)

deriving instance
  ( ShowQ p
  ) => Show (FunDecl p)

deriving instance
  ( ShowQ p
  ) => Show (FunCase p)

deriving instance
  ( ShowQ p
  ) => Show (FunField p)

deriving instance
  ( ShowQ p
  ) => Show (EnvDecl p)

deriving instance
  ( ShowQ p
  ) => Show (EnvCtorDecl p)

deriving instance
  ( ShowQ p
  ) => Show (SetGroupDecl p)

deriving instance
  ( ShowQ p
  ) => Show (SetDecl p)

deriving instance
  ( ShowQ p
  ) => Show (SetCtorDecl p)

deriving instance
  ( ShowQ p
  ) => Show (SetFieldDecl p)

deriving instance
  ( ShowQ p
  , Show (PhFormJudgementOutputs p)
  ) => Show (RelationGroupDecl p)

deriving instance
  ( ShowQ p
  , Show (PhFormJudgementOutputs p)
  ) => Show (RelationDecl p)

deriving instance
  ( Eq (PhSortVariable p)
  , Eq (PhFreeVariable p)
  , Eq (PhSetVariable p)
  , Eq (PhBindingVariable p)
  , Eq (PhBindSpecInf p)
  ) => Eq (RuleMetavarBinder p)

deriving instance
  ( Ord (PhSortVariable p)
  , Ord (PhFreeVariable p)
  , Ord (PhSetVariable p)
  , Ord (PhBindingVariable p)
  , Ord (PhBindSpecInf p)
  ) => Ord (RuleMetavarBinder p)

deriving instance
  ( ShowQ p
  ) => Show (RuleMetavarBinder p)

deriving instance
  ( ShowQ p
  , Show (PhFormJudgementOutputs p)
  ) => Show (Rule p)

deriving instance
  ( ShowQ p
  , Show (PhFormJudgementOutputs p)
  ) => Show (Formula p)

deriving instance
  ( ShowQ p
  ) => Show (Judgement p)

deriving instance
  ( ShowQ p
  ) => Show (RuleBindSpecItem p)

deriving instance
  ( ShowQ p
  ) => Show (SymbolicTerm p)

deriving instance
  ( ShowQ p
  ) => Show (SymbolicEnv p)

deriving instance
  ( ShowQ p
  ) => Show (SymbolicField w p)

deriving instance
  () => Show (SymbolicSet p)
