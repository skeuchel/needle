{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}

module KnotCore.Syntax where

import Data.List (intercalate)
import Data.Map (Map)

--  __  __     _
-- |  \/  |___| |_ __ _ _ _  __ _ _ __  ___ ___
-- | |\/| / -_)  _/ _` | ' \/ _` | '  \/ -_|_-<
-- |_|  |_\___|\__\__,_|_||_\__,_|_|_|_\___/__/

{-
newtype NamespaceTypeName = NTN { fromNTN :: String }
  deriving (Eq,Ord)
instance Read NamespaceTypeName where
  readPrec = fmap NTN readPrec
instance Show NamespaceTypeName where
  showsPrec i (NTN s) = showsPrec i s

newtype SortTypeName = STN { fromSTN :: String }
  deriving (Eq,Ord)
instance Read SortTypeName where
  readPrec = fmap STN readPrec
instance Show SortTypeName where
  showsPrec i (STN s) = showsPrec i s

newtype EnvTypeName = ETN { fromETN :: String }
  deriving (Eq,Ord)
instance Read EnvTypeName where
  readPrec = fmap ETN readPrec
instance Show EnvTypeName where
  showsPrec i (ETN s) = showsPrec i s
-}

data CtorName
  = CNS { fromCN :: String, cnSort :: SortTypeName  }
  | CNE { fromCN :: String, cnEnv  :: EnvTypeName  }
  | CNO { fromCN :: String }
  deriving (Eq,Ord)
instance Show CtorName where showsPrec i = showsPrec i . fromCN

newtype NameRoot = NR { fromNR :: String }
  deriving (Eq,Ord)
instance Show NameRoot where showsPrec i = showsPrec i . fromNR

type Suffix = String

newtype NamespaceTypeName = NTN { fromNtn :: String }
  deriving (Eq,Ord,Show)

newtype SortGroupTypeName = SGTN { fromSgtn :: String }
  deriving (Eq,Ord,Show)

newtype SortTypeName = STN { fromStn :: String }
  deriving (Eq,Ord,Show)

newtype EnvTypeName = ETN { fromEtn :: String }
  deriving (Eq,Ord,Show)

newtype RelationTypeName = RTN { fromRtn :: String }
  deriving (Eq,Ord,Show)

data FunGroupName = FGN { fromFgn :: String }
  deriving (Eq,Ord,Show)

data FunName
  = FN {
      fnName                    ::  String,
      fnSort                    ::  SortTypeName,
      fnNamespaces              ::  [NamespaceTypeName]
    }
  deriving (Eq,Ord,Show)

data SubtreeVar
  = SubtreeVar {
      stvRoot               ::  NameRoot,
      stvSuffix             ::  Suffix,
      stvTypeName           ::  SortTypeName
    }
  deriving (Eq,Ord,Show)

data MetavarVar
  = MetavarVar {
      mvvRoot                   ::  NameRoot,
      mvvSuffix                 ::  Suffix,
      mvvTypeName               ::  NamespaceTypeName
    }
  deriving (Eq,Ord,Show)

data EnvVar
  = EnvVar {
      envVarRoot                   ::  NameRoot,
      envVarSuffix                 ::  Suffix,
      envVarTypeName               ::  EnvTypeName
    }
  deriving (Eq,Ord,Show)

--  ___              _  __ _         _   _
-- / __|_ __  ___ __(_)/ _(_)__ __ _| |_(_)___ _ _
-- \__ \ '_ \/ -_) _| |  _| / _/ _` |  _| / _ \ ' \
-- |___/ .__/\___\__|_|_| |_\__\__,_|\__|_\___/_||_|
--     |_|

data TermSpec
  = TermSpec {
      tsNamespaceDecls        :: [NamespaceDecl],
      tsFunctionEnv           :: FunctionEnv,
      tsSortGroupDecls        :: [SortGroupDecl],
      tsFunGroupDecls         :: [FunGroupDecl],
      tsEnvDecls              :: [EnvDecl],
      tsRelDecls              :: [RelationDecl]
    }
  deriving (Eq,Ord,Show)

--  _  _
-- | \| |__ _ _ __  ___ ____ __  __ _ __ ___ ___
-- | .` / _` | '  \/ -_|_-< '_ \/ _` / _/ -_|_-<
-- |_|\_\__,_|_|_|_\___/__/ .__/\__,_\__\___/__/
--                        |_|

data NamespaceDecl
  = NamespaceDecl {
      nsdTypeName             ::  NamespaceTypeName,
      nsdNameRoots            ::  [NameRoot],
      nsdSort                 ::  SortTypeName,
      nsdCtor                 ::  CtorName,
      nsdShiftRoot            ::  String,
      nsdSubstRoot            ::  String
    }
  deriving (Eq,Ord,Show)

type SortFunctionEnv = Map FunName [NamespaceTypeName]
type FunctionEnv     = Map SortTypeName SortFunctionEnv

--  ___          _
-- / __| ___ _ _| |_ ___
-- \__ \/ _ \ '_|  _(_-<
-- |___/\___/_|  \__/__/

data SortGroupDecl
  = SortGroupDecl {
      sgTypeName              ::  SortGroupTypeName,
      sgSorts                 ::  [SortDecl],
      sgNamespaces            ::  [NamespaceTypeName],
      sgHasBindSpec           ::  Bool
    }
  deriving (Eq,Ord,Show)

data SortDecl
  = SortDecl {
      sdTypeName            ::  SortTypeName,
      sdNameRoots           ::  [NameRoot],
      sdCtors               ::  [CtorDecl]
    }
  deriving (Eq,Ord,Show)

data CtorDecl
  = CtorVar {
      cdName                ::  CtorName,
      cdMetavar             ::  MetavarVar
    }
  | CtorTerm {
      cdName                ::  CtorName,
      cdFields              ::  [FieldDecl]
    }
  deriving (Eq,Ord,Show)

data FieldDecl
  = FieldSubtree {
      fieldSubtreeVar  :: SubtreeVar,
      fieldBindSpec    :: BindSpec
    }
  | FieldBinding {
      fieldMetavarVar :: MetavarVar
    }
  deriving (Eq,Ord,Show)

--  ___ _         _
-- | _ |_)_ _  __| |____ __  ___ __ ___
-- | _ \ | ' \/ _` (_-< '_ \/ -_) _(_-<
-- |___/_|_||_\__,_/__/ .__/\___\__/__/
--                    |_|

-- Heterogeneous list of items
type BindSpec = [VleItem]

-- Homogeneous list of items
type Vle = [VleItem]

data VleItem
  = VleBinding {
      vleNamespace            ::  [NamespaceTypeName],
      vleMetavar              ::  MetavarVar
    }
  | VleCall {
      vleNamespace            ::  [NamespaceTypeName],
      vleFunName              ::  FunName,
      vleSubTree              ::  SubtreeVar
    }
  deriving (Eq,Ord,Show)

--  ___             _   _
-- | __|  _ _ _  __| |_(_)___ _ _  ___
-- | _| || | ' \/ _|  _| / _ \ ' \(_-<
-- |_| \_,_|_||_\__|\__|_\___/_||_/__/

data FunGroupDecl
  = FunGroupDecl {
      fgdName              ::  FunGroupName,
      fgdSortGroup         ::  SortGroupTypeName,
      fgdFuns              ::  [(SortTypeName,[FunDecl])]
    }
  deriving (Eq,Ord,Show)

data FunDecl
  = FunDecl {
      fdName      :: FunName,
      fdSource    :: SortTypeName,
      fdTarget    :: [NamespaceTypeName],
      fdMatchItem :: SubtreeVar,
      fdCases     :: [FunCase]
    }
  deriving (Eq,Ord,Show)

data FunCase
  = FunCase {
      fcCtor   :: CtorName,
      fcFields :: [FieldMetaBinding],
      fcRhs    :: Vle
    }
  deriving (Eq,Ord,Show)

data FieldMetaBinding
  = FieldMetaBindingSubtree {
      fmbSubtreeVar :: SubtreeVar
    }
  | FieldMetaBindingMetavar {
      fmbMetavarVar :: MetavarVar
    }
  | FieldMetaBindingOutput {
      fmbEnvVar     :: EnvVar
    }
  deriving (Eq,Ord,Show)

--  ___         _                            _
-- | __|_ ___ _(_)_ _ ___ _ _  _ __  ___ _ _| |_ ___
-- | _|| ' \ V / | '_/ _ \ ' \| '  \/ -_) ' \  _(_-<
-- |___|_||_\_/|_|_| \___/_||_|_|_|_\___|_||_\__/__/

data EnvDecl
  = EnvDecl {
      edTypeName             :: EnvTypeName,
      edNameRoots            :: [NameRoot],
      edCtors                :: [EnvCtor]
    }
  deriving (Eq,Ord,Show)

data EnvCtor
  = EnvCtorNil {
      ecName             :: CtorName
    }
  | EnvCtorCons {
      ecName             :: CtorName,
      ecMetavar          :: MetavarVar,
      ecFields           :: [SubtreeVar]
    }
  deriving (Eq,Ord,Show)

--  ___     _      _   _
-- | _ \___| |__ _| |_(_)___ _ _  ___
-- |   / -_) / _` |  _| / _ \ ' \(_-<
-- |_|_\___|_\__,_|\__|_\___/_||_/__/

data RelationDecl
  = RelationDecl {
      relEnv      :: Maybe EnvVar,
      relTypeName :: RelationTypeName,
      relIndices  :: [SortTypeName],
      relRules    :: [Rule]
    }
  deriving (Eq,Ord,Show)

data Rule
  = Rule {
      ruleName          :: CtorName,
      ruleFieldsBinders :: [FieldMetaBinding],
      rulePremises      :: [Formula],
      ruleConclusion    :: Judgement,
      ruleBindings      :: [RuleBinding]
    }
  deriving (Eq,Ord,Show)

data RuleBinding
  = RuleBinding {
      rbMetavar      :: MetavarVar,
      rbTerms        :: [SymbolicTerm]
    }
  deriving (Eq,Ord,Show)

data Formula
  = FormBinding {
      fmlBinding     :: RuleBinding
    }
  | FormJudgement {
      fmlJmtBindings    :: [RuleBinding],
      fmlJmtTypeName    :: RelationTypeName,
      fmlJmtEnvTypeName :: Maybe EnvVar,
      fmlJmtTerms       :: [SymbolicTerm]
    }
  deriving (Eq,Ord,Show)

data Judgement
  = Judgement {
      jmtTypeName    :: RelationTypeName,
      jmtEnvTypeName :: Maybe EnvVar,
      jmtTerms       :: [SymbolicTerm]
    }
  deriving (Eq,Ord,Show)

--  ___            _         _ _      _
-- / __|_  _ _ __ | |__  ___| (_)__  | |_ ___ _ _ _ __  ___
-- \__ \ || | '  \| '_ \/ _ \ | / _| |  _/ -_) '_| '  \(_-<
-- |___/\_, |_|_|_|_.__/\___/_|_\__|  \__\___|_| |_|_|_/__/
--      |__/

data SymbolicTerm
  = SymBinding {
      stMetavarBind  :: MetavarVar
    }
  | SymSubtree {
      stSubtree      :: SubtreeVar
    }
  | SymEnv {
      stEnvVar       :: EnvVar
    }
  | SymCtorVar {
      stCtor         :: CtorName,
      stMetavarRef   :: MetavarVar
    }
  | SymCtorTerm {
      stCtor         :: CtorName,
      stFields       :: [SymbolicTerm]
    }
  | SymSubst {
      stVar          :: MetavarVar,
      stSubstitute   :: SymbolicTerm,
      stSubstitutee  :: SymbolicTerm
    }
  deriving (Eq,Ord,Show)

--  _____
-- |_   _|  _ _ __  ___   _ _  __ _ _ __  ___ ___
--   | || || | '_ \/ -_) | ' \/ _` | '  \/ -_|_-<
--   |_| \_, | .__/\___| |_||_\__,_|_|_|_\___/__/
--       |__/|_|

class TypeNameOf a b | a -> b where
  typeNameOf :: a -> b
instance TypeNameOf MetavarVar NamespaceTypeName where
  typeNameOf (MetavarVar _ _ ntn) = ntn
instance TypeNameOf SubtreeVar SortTypeName where
  typeNameOf (SubtreeVar _ _ stn) = stn
instance TypeNameOf SortDecl SortTypeName where
  typeNameOf (SortDecl stn _ _) = stn
instance TypeNameOf NamespaceDecl NamespaceTypeName where
  typeNameOf (NamespaceDecl ntn _ _ _ _ _) = ntn
instance TypeNameOf SortGroupDecl SortGroupTypeName where
  typeNameOf = sgTypeName
instance TypeNameOf EnvDecl EnvTypeName where
  typeNameOf = edTypeName

groupName :: [SortTypeName] -> SortGroupTypeName
groupName stns = SGTN (intercalate "_" $ map fromStn stns)

funGroupName :: [FunName] -> FunGroupName
funGroupName fns = FGN (intercalate "_" $ map fnName fns)
