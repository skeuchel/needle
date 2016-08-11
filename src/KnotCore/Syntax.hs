{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -Wall #-}

module KnotCore.Syntax
  ( module Knot.Common
  , module KnotCore.Syntax
  ) where

import Knot.Common hiding
  ( Identifier
  , FN
  )

import Data.Map (Map)

--  __  __     _
-- |  \/  |___| |_ __ _ _ _  __ _ _ __  ___ ___
-- | |\/| / -_)  _/ _` | ' \/ _` | '  \/ -_|_-<
-- |_|  |_\___|\__\__,_|_||_\__,_|_|_|_\___/__/

data LookupVar
  = LookupVar
    { lookupVarRoot                ::  NameRoot
    , lookupVarSuffix              ::  Suffix
    , lookupVarEnv                 ::  SymbolicEnv
    , lookupVarReference           ::  FreeVariable
    , lookupVarIndices             ::  [SymbolicField 'WOMV]
    }
  deriving (Eq,Ord,Show)

data Hypothesis =
  Hypothesis
  { hypNameRoot  :: NameRoot
  , hypSuffix    :: Suffix
  }
  deriving (Eq,Ord,Show)

--  ___              _  __ _         _   _
-- / __|_ __  ___ __(_)/ _(_)__ __ _| |_(_)___ _ _
-- \__ \ '_ \/ -_) _| |  _| / _/ _` |  _| / _ \ ' \
-- |___/ .__/\___\__|_|_| |_\__\__,_|\__|_\___/_||_|
--     |_|

data TermSpec
  = TermSpec
    { tsNamespaceDecls        :: [NamespaceDecl]
    , tsFunctionEnv           :: FunctionEnv
    , tsSortGroupDecls        :: [SortGroupDecl]
    , tsFunGroupDecls         :: [FunGroupDecl]
    , tsEnvDecls              :: [EnvDecl]
    , tsRelGroupDecls         :: [RelationGroupDecl]
    , tsSetGroupDecls         :: [SetGroupDecl]
    , tsSubstitutableClauses  :: [SubstitutableClauseInfo]
    }
  deriving (Eq,Ord,Show)

--  _  _
-- | \| |__ _ _ __  ___ ____ __  __ _ __ ___ ___
-- | .` / _` | '  \/ -_|_-< '_ \/ _` / _/ -_|_-<
-- |_|\_\__,_|_|_|_\___/__/ .__/\__,_\__\___/__/
--                        |_|

data NamespaceDecl
  = NamespaceDecl
    { nsdTypeName             ::  NamespaceTypeName
    , nsdNameRoots            ::  [NameRoot]
    , nsdSort                 ::  SortTypeName
    , nsdCtor                 ::  CtorName
    , nsdShiftRoot            ::  String
    , nsdSubstRoot            ::  String
    }
  deriving (Eq,Ord,Show)

type SortFunctionEnv = Map FunName [NamespaceTypeName]
type FunctionEnv     = Map SortTypeName SortFunctionEnv

--  ___          _
-- / __| ___ _ _| |_ ___
-- \__ \/ _ \ '_|  _(_-<
-- |___/\___/_|  \__/__/

data SortGroupDecl
  = SortGroupDecl
    { sgTypeName                ::  SortGroupTypeName
    , sgSorts                   ::  [SortDecl]
    , sgNamespaces              ::  [NamespaceTypeName]
    , sgHasBindSpec             ::  Bool
    }
  deriving (Eq,Ord,Show)

data SortDecl
  = SortDecl
    { sdTypeName                ::  SortTypeName
    , sdNameRoots               ::  [NameRoot]
    , sdCtors                   ::  [CtorDecl]
    }
  deriving (Eq,Ord,Show)

data CtorDecl
  = CtorVar
    { ctorDeclName              ::  CtorName
    , ctorDeclFreeVariable      ::  FreeVariable
    , ctorDeclFreeVariableWf    ::  Hypothesis
    }
  | CtorReg
    { ctorDeclName              ::  CtorName
    , ctorDeclFields            ::  [FieldDecl 'WMV]
    }
  deriving (Eq,Ord,Show)

data FieldDecl (w :: WithMV)
  = FieldDeclSort
    { fieldDeclBindSpec         ::  BindSpec
    , fieldDeclSortVariable     ::  SortVariable
    , fieldDeclSortVariableWf   ::  Hypothesis
    }
  | FieldDeclEnv
    { fieldDeclBindSpec         ::  BindSpec
    , fieldDeclEnvVariable      ::  EnvVariable
    , fieldDeclEnvVariableWf    ::  Hypothesis
    }
  | FieldDeclSet
    { fieldDeclSetVariable      ::  SetVariable
    }
  | (w ~ 'WMV) =>
    FieldDeclBinding
    { fieldDeclBindSpec         ::  BindSpec
    , fieldDeclBindingVariable  ::  BindingVariable
    }
  | (w ~ 'WMV) =>
    FieldDeclReference
    { fieldDeclFreeVariable     ::  FreeVariable
    , fieldDeclFreeVariableWf   ::  Hypothesis
    }

deriving instance Eq (FieldDecl w)
deriving instance Ord (FieldDecl w)
deriving instance Show (FieldDecl w)

--  ___      _
-- / __| ___| |_ ___
-- \__ \/ -_)  _(_-<
-- |___/\___|\__/__/

data SetGroupDecl
  = SetGroupDecl
    { zgdSets                   ::  [SetDecl]
    }
  deriving (Eq,Ord,Show)

data SetDecl
  = SetDecl
    { zdTypeName                ::  SetTypeName
    , zdNameRoots               ::  [NameRoot]
    , zdCtors                   ::  [SetCtorDecl]
    }
  deriving (Eq,Ord,Show)

data SetCtorDecl
  = SetCtor
    { setCtorName               ::  CtorName
    , setCtorFields             ::  [SetFieldDecl]
    }
  deriving (Eq,Ord,Show)

data SetFieldDecl
  = SetFieldDecl
    { setFieldDeclLoc           ::  Loc
    , setFieldDeclSetVariable   ::  SetVariable
    }
  deriving (Eq,Ord,Show)

--  ___ _         _
-- | _ |_)_ _  __| |____ __  ___ __ ___
-- | _ \ | ' \/ _` (_-< '_ \/ -_) _(_-<
-- |___/_|_||_\__,_/__/ .__/\___\__/__/
--                    |_|

-- Heterogeneous list of items
type BindSpec = SnocList BindSpecItem

data BindSpecItem
  = BsiBinding
    { bsiBindingVariable        ::  BindingVariable
    }
  | BsiCall
    { bsiFunName                ::  FunName
    , bsiSortVariable           ::  SortVariable
    }
  deriving (Eq,Ord,Show)

--  ___             _   _
-- | __|  _ _ _  __| |_(_)___ _ _  ___
-- | _| || | ' \/ _|  _| / _ \ ' \(_-<
-- |_| \_,_|_||_\__|\__|_\___/_||_/__/

data FunGroupDecl
  = FunGroupDecl
    { fgdName                   ::  FunGroupName
    , fgdSortGroup              ::  SortGroupTypeName
    , fgdFuns                   ::  [(SortTypeName,[FunDecl])]
    }
  deriving (Eq,Ord,Show)

data FunDecl
  = FunDecl
    { fdName                    ::  FunName
    , fdSource                  ::  SortTypeName
    , fdTarget                  ::  [NamespaceTypeName]
    , fdCases                   ::  [FunCase]
    }
  deriving (Eq,Ord,Show)

data FunCase
  = FunCase
    { fcCtor                    ::  CtorName
    , fcFields                  ::  [FunField]
    , fcRhs                     ::  BindSpec
    }
  deriving (Eq,Ord,Show)

data FunField
  = FunFieldSort
    { ffBindSpec                ::  BindSpec
    , ffSortVariable            ::  SortVariable
    }
  | FunFieldBinding
    { ffBindSpec                ::  BindSpec
    , ffBindingVariable         ::  BindingVariable
    }
  | FunFieldEnv
    { ffBindSpec                ::  BindSpec
    , ffEnvVariable             ::  EnvVariable
    }
  | FunFieldReference
    { ffFreeVariable            ::  FreeVariable
    }
  deriving (Eq,Ord,Show)

--  ___         _                            _
-- | __|_ ___ _(_)_ _ ___ _ _  _ __  ___ _ _| |_ ___
-- | _|| ' \ V / | '_/ _ \ ' \| '  \/ -_) ' \  _(_-<
-- |___|_||_\_/|_|_| \___/_||_|_|_|_\___|_||_\__/__/

data EnvDecl
  = EnvDecl
    { edTypeName                ::  EnvTypeName
    , edNameRoots               ::  [NameRoot]
    , edCtors                   ::  [EnvCtor]
    }
  deriving (Eq,Ord,Show)

data EnvCtor
  = EnvCtorNil
    { envCtorName               ::  CtorName
    }
  | EnvCtorCons
    { envCtorName               ::  CtorName
    , envCtorBindingVariable    ::  BindingVariable
    , envCtorFields             ::  [FieldDecl 'WOMV]
    , envCtorSubst              ::  Maybe EnvCtorSubst
    }
  deriving (Eq,Ord,Show)

data EnvCtorSubst
  = EnvCtorSubst
    { envCtorSubstRelation      ::  RelationTypeName
    , envCtorSubstVarRule       ::  Maybe CtorName
    }
  deriving (Eq,Ord,Show)

--  ___     _      _   _
-- | _ \___| |__ _| |_(_)___ _ _  ___
-- |   / -_) / _` |  _| / _ \ ' \(_-<
-- |_|_\___|_\__,_|\__|_\___/_||_/__/

data RelationGroupDecl
  = RelationGroupDecl
    { rgEnv                     ::  Maybe EnvTypeName
    , rgRelations               ::  [RelationDecl]
    }
  deriving (Eq,Ord,Show)

data RelationDecl
  = RelationDecl
    { relEnv                    ::  Maybe EnvVariable
    , relTypeName               ::  RelationTypeName
    , relIndices                ::  [FieldDecl 'WOMV]
    , relNameRoots              ::  [NameRoot]
    , relOutputs                ::  [(FunName,EnvTypeName)]
    , relRules                  ::  [Rule]
    }
  deriving (Eq,Ord,Show)

data RuleMetavarBinder
  = RuleMetavarSort
    { rmbBindspec               ::  BindSpec
    , rmbSortVariable           ::  SortVariable
    , rmbSortVariableWf         ::  Hypothesis
    , rmbSortVariablePos        ::  Maybe SortVariablePos
    }
  | RuleMetavarEnv
    { rmbBindspec               ::  BindSpec
    , rmbEnvVariable            ::  EnvVariable
    , rmbEnvVariableWf          ::  Hypothesis
    }
  | RuleMetavarBinding
    { rmbBindspec               ::  BindSpec
    , rmbBindingVariable        ::  BindingVariable
    }
  | RuleMetavarFree
    { rmbFreeVariable           ::  FreeVariable
    , rmbFreeVariableWf         ::  Hypothesis
    }
  -- These are meta-bindings for the outputs of the premises. It's not used for
  -- the conclusion.
  | RuleMetavarOutput
    { rmbRuleBindspec           ::  RuleBindSpec
    , rmbEnvVariable            ::  EnvVariable
    }
  | RuleMetavarSet
    { rmbSetVariable            ::  SetVariable
    }
  deriving (Eq,Ord,Show)

data Rule
  = RuleVar
    { ruleName                  ::  CtorName
    , ruleMetavarBinders        ::  [RuleMetavarBinder]
    , ruleVarEnvTypeName        ::  EnvTypeName
    , ruleVarFreeVariable       ::  FreeVariable
    , ruleVarData               ::  [SymbolicField 'WOMV]
    , ruleConclusion            ::  Judgement
    }
  | RuleReg
    { ruleName                  ::  CtorName
    , ruleMetavarBinders        ::  [RuleMetavarBinder]
    , rulePremises              ::  [Formula]
    , ruleConclusion            ::  Judgement
    , ruleOutputs               ::  [(FunName, RuleBindSpec)]
    }
  deriving (Eq,Ord,Show)

data Formula
  = FormLookup
    { fmlLookupVar              ::  LookupVar
    , fmlLookupEnv              ::  EnvVariable
    , fmlLookupFreeVariable     ::  FreeVariable
    , fmlLookupData             ::  [SymbolicField 'WOMV]
    }
  | FormJudgement
    { fmlJmtVariable            ::  JudgementVariable
    , fmlJmtBindSpec            ::  RuleBindSpec
    , fmlJmtJudgement           ::  Judgement
    -- This is not used for the conclusion, because it would need to be a
    -- symbolic environtment. Instead the output RuleBindSpecs in the Rule
    -- declaration itself are used. Best would be to inline the conclusion
    -- judgement into the rule declarations.
    , fmlJmtOutputs             ::  [(FunName, EnvVariable)]
    }
  deriving (Eq,Ord,Show)

type RuleBindSpec = SnocList RuleBindSpecItem
data RuleBindSpecItem
  = RuleBsiBinding
    { rbsiBindingVariable       ::  BindingVariable
    , rbsiTerms                 ::  [SymbolicField 'WOMV]
    }
  | RuleBsiCall
    { rbsiFunName               ::  FunName
    , rbsiJudgement             ::  JudgementVariable
    }
  deriving (Eq,Ord,Show)

data Judgement
  = Judgement
    { jmtTypeName               ::  RelationTypeName
    , jmtEnv                    ::  Maybe SymbolicEnv
    , jmtFields                 ::  [SymbolicField 'WOMV]
    , jmtOutputs                ::  [(FunName, SymbolicEnv)]
    }
  deriving (Eq,Ord,Show)

--  ___            _         _ _      _
-- / __|_  _ _ __ | |__  ___| (_)__  | |_ ___ _ _ _ __  ___
-- \__ \ || | '  \| '_ \/ _ \ | / _| |  _/ -_) '_| '  \(_-<
-- |___/\_, |_|_|_|_.__/\___/_|_\__|  \__\___|_| |_|_|_/__/
--      |__/

data SymbolicTerm
  = SymSubtree
    { stScope                   ::  BindSpec -- Current scope
    , stSortVar                 ::  SortVariable
    }
  | SymCtorVarFree
    { stScope                   ::  BindSpec -- Current scope
    , stCtor                    ::  CtorName
    , stFreeVariable            ::  FreeVariable
    }
  | SymCtorVarBound
    { stScope                   ::  BindSpec -- Current scope
    , stCtor                    ::  CtorName
    , stBindingVariable         ::  BindingVariable
    , stBindingBindSpec         ::  BindSpec -- Scope where the BV was introduced
    , stBindingBindSpecDiff     ::  BindSpec -- Difference to the current scope
    }
  | SymCtorReg
    { stScope                   ::  BindSpec -- Current (outer) scope
    , stCtorName                ::  CtorName
    , stFields                  ::  [SymbolicField 'WMV]
    }
  | SymWeaken
    { stScope                   ::  BindSpec -- Current (outer) scope
    , stWeakenInnerScope        ::  BindSpec -- Current (outer) scope
    , stWeakenTerm              ::  SymbolicTerm
    , stWeakenBindSpecDiff      ::  BindSpec
    }
  | SymSubst
    { stScope                   ::  BindSpec -- Current scope
    , stSubstBindingVariable    ::  BindingVariable
    , stSubstitute              ::  SymbolicTerm
    , stSubstitutee             ::  SymbolicTerm
    }
  deriving (Eq,Ord,Show)

data SymbolicCoTerm
  = SymCoHole
    { sctTypeName               ::  SortTypeName
    }
  | SymCoCtorReg
    { sctScope                  ::  BindSpec
    , sctBindspec               ::  BindSpec
    , sctCtor                   ::  CtorName
    , sctPreFields              ::  [SymbolicField 'WMV]
    , sctRec                    ::  SymbolicCoTerm
    , sctPostFields             ::  [SymbolicField 'WMV]
    }
  deriving (Eq,Ord,Show)

plug :: SymbolicTerm -> SymbolicCoTerm -> SymbolicTerm
plug t (SymCoHole{}) = t
plug t (SymCoCtorReg scp bs cn pre sct post) =
  SymCtorReg scp cn (pre ++ [SymFieldSort scp bs (plug t sct)] ++ post)

data SortVariablePos
  = SortVariablePos
    { svpJudgementVariable      ::  JudgementVariable
    , svpJudgementBindSpec      ::  RuleBindSpec
    , svpJudgement              ::  Judgement
    , svpPreTerms               ::  [SymbolicField 'WOMV]
    , svpRec                    ::  SymbolicCoTerm
    , svpPostTerms              ::  [SymbolicField 'WOMV]
    }
  deriving (Eq,Ord,Show)

data SymbolicField (w :: WithMV)
  = SymFieldSort
    { symFieldScope             ::  BindSpec     -- Scope of this node
    , symFieldBindSpec          ::  BindSpec     -- Binding specification
                                                 -- of this field
    , symFieldSymbolicTerm      ::  SymbolicTerm
    }
  | SymFieldEnv
    { symFieldScope             ::  BindSpec     -- Scope of this node
    , symFieldBindSpec          ::  BindSpec     -- Binding specification
                                                 -- of this field
    , symFieldSymbolicEnv       ::  SymbolicEnv
    }
  | (w ~ 'WMV) =>
    SymFieldBinding
    { symFieldScope             ::  BindSpec     -- Scope of this node
    , symFieldBindingVariable   ::  BindingVariable
    }
  | (w ~ 'WMV) =>
    SymFieldReferenceFree
    { symFieldScope             ::  BindSpec
    , symFieldFreeVariable      ::  FreeVariable
    }
  | (w ~ 'WMV) =>
    SymFieldReferenceBound
    { symFieldScope             ::  BindSpec
    , symFieldBindingVariable   ::  BindingVariable
    }

deriving instance Eq (SymbolicField w)
deriving instance Ord (SymbolicField w)
deriving instance Show (SymbolicField w)

data SymbolicEnv
  = SymEnvVar
    { seEnvVar                  ::  EnvVariable
    }
  | SymEnvNil
    { seEnvTypeName             ::  EnvTypeName
    }
  | SymEnvCons
    { seNamespace               ::  NamespaceTypeName
    , seTail                    ::  SymbolicEnv
    , seIndices                 ::  [SymbolicField 'WOMV]
    }
  | SymEnvAppend
    { seAppendLeft              ::  SymbolicEnv
    , seAppendRight             ::  SymbolicEnv
    }
  -- | SymEnvCall
  --   { seFunName                 ::  FunName
  --   , seJudgementVariable       ::  JudgementVariable
  --   }
  deriving (Eq,Ord,Show)

--  _____
-- |_   _|  _ _ __  ___   _ _  __ _ _ __  ___ ___
--   | || || | '_ \/ -_) | ' \/ _` | '  \/ -_|_-<
--   |_| \_, | .__/\___| |_||_\__,_|_|_|_\___/__/
--       |__/|_|

instance TypeNameOf SortDecl SortTypeName where
  typeNameOf (SortDecl stn _ _) = stn
instance TypeNameOf NamespaceDecl NamespaceTypeName where
  typeNameOf (NamespaceDecl ntn _ _ _ _ _) = ntn
instance TypeNameOf SortGroupDecl SortGroupTypeName where
  typeNameOf = sgTypeName
instance TypeNameOf EnvDecl EnvTypeName where
  typeNameOf = edTypeName
