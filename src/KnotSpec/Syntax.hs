

-- UUAGC 0.9.52.1 (src/KnotSpec/Syntax.ag)
module KnotSpec.Syntax( module KnotSpec.Syntax.Core
, module KnotSpec.Syntax
) where

{-# LINE 9 "src/KnotSpec/Syntax.ag" #-}

import KnotSpec.Syntax.Core
import Data.Map (Map)
{-# LINE 13 "src/KnotSpec/Syntax.hs" #-}
-- BindSpec ----------------------------------------------------
type BindSpec = [VleItem]
-- CtorDecl ----------------------------------------------------
data CtorDecl = CtorVar (CtorName) (Name)
              | CtorTerm (CtorName) (FieldDecls)
              deriving ( Eq,Ord,Read,Show)
-- CtorDecls ---------------------------------------------------
type CtorDecls = [CtorDecl]
-- EnvCtor -----------------------------------------------------
data EnvCtor = EnvCtorNil (CtorName)
             | EnvCtorCons (CtorName) (Name) (Names)
             deriving ( Eq,Ord,Read,Show)
-- EnvCtors ----------------------------------------------------
type EnvCtors = [EnvCtor]
-- EnvDecl -----------------------------------------------------
data EnvDecl = EnvDecl (TypeName) (NameRoots) (EnvCtors)
             deriving ( Eq,Ord,Read,Show)
-- EnvDecls ----------------------------------------------------
type EnvDecls = [EnvDecl]
-- FieldDecl ---------------------------------------------------
data FieldDecl = FieldDecl (BindSpec) (Name)
               deriving ( Eq,Ord,Read,Show)
-- FieldDecls --------------------------------------------------
type FieldDecls = [FieldDecl]
-- Formula -----------------------------------------------------
data Formula = FormBinding (RuleBinding)
             | FormJudgement (RuleBindings) (Judgement)
             deriving ( Eq,Ord,Read,Show)
-- Formulas ----------------------------------------------------
type Formulas = [Formula]
-- FunCase -----------------------------------------------------
data FunCase = FunCase (CtorName) (Names) (Vle)
             deriving ( Eq,Ord,Read,Show)
-- FunCases ----------------------------------------------------
type FunCases = [FunCase]
-- FunDecl -----------------------------------------------------
data FunDecl = FunDecl (FunName) (TypeName) (TypeNames) (FunCases)
             deriving ( Eq,Ord,Read,Show)
-- FunDecls ----------------------------------------------------
type FunDecls = [FunDecl]
-- Judgement ---------------------------------------------------
data Judgement = Judgement (TypeName) (SymbolicTerms)
               deriving ( Eq,Ord,Read,Show)
-- Judgements --------------------------------------------------
type Judgements = [Judgement]
-- MEEnvNameRoots ----------------------------------------------
type MEEnvNameRoots = Data.Map.Map ((TypeName)) (NameRoots)
-- MEEnvTypeName -----------------------------------------------
type MEEnvTypeName = Data.Map.Map ((NameRoot)) (TypeName)
-- MEFunType ---------------------------------------------------
type MEFunType = Data.Map.Map ((FunName)) (((TypeName,TypeNames)))
-- MENamespaceCtor ---------------------------------------------
type MENamespaceCtor = Data.Map.Map ((TypeName)) (((TypeName,CtorName)))
-- MENamespaceNameRoots ----------------------------------------
type MENamespaceNameRoots = Data.Map.Map ((TypeName)) (NameRoots)
-- MENamespaceTypeName -----------------------------------------
type MENamespaceTypeName = Data.Map.Map ((NameRoot)) (TypeName)
-- MERelationEnv -----------------------------------------------
type MERelationEnv = Data.Map.Map ((TypeName)) ((TypeName))
-- MESortNameRoots ---------------------------------------------
type MESortNameRoots = Data.Map.Map ((TypeName)) (NameRoots)
-- MESortTypeName ----------------------------------------------
type MESortTypeName = Data.Map.Map ((NameRoot)) (TypeName)
-- MbString ----------------------------------------------------
type MbString = Maybe ((String))
-- MbTypeName --------------------------------------------------
type MbTypeName = Maybe (TypeName)
-- Name --------------------------------------------------------
type Name = ( (NameRoot),(Suffix))
-- NameRoots ---------------------------------------------------
type NameRoots = [(NameRoot)]
-- Names -------------------------------------------------------
type Names = [Name]
-- NamespaceDecl -----------------------------------------------
data NamespaceDecl = NamespaceDecl (TypeName) (NameRoots) (TypeName) (NamespaceDirectives)
                   deriving ( Eq,Ord,Read,Show)
-- NamespaceDecls ----------------------------------------------
type NamespaceDecls = [NamespaceDecl]
-- NamespaceDirective ------------------------------------------
data NamespaceDirective = NamespaceShift (String)
                        | NamespaceSubst (String)
                        | NamespaceWeaken (String)
                        | NamespaceCutoff (String)
                        deriving ( Eq,Ord,Read,Show)
-- NamespaceDirectives -----------------------------------------
type NamespaceDirectives = [NamespaceDirective]
-- RelationDecl ------------------------------------------------
data RelationDecl = RelationDecl (MbTypeName) (TypeName) (TypeNames) (Rules)
                  deriving ( Eq,Ord,Read,Show)
-- RelationDecls -----------------------------------------------
type RelationDecls = [RelationDecl]
-- Rule --------------------------------------------------------
data Rule = Rule (CtorName) (Formulas) (Judgement) (RuleBindings)
          deriving ( Eq,Ord,Read,Show)
-- RuleBinding -------------------------------------------------
data RuleBinding = RuleBinding (Name) (SymbolicTerms)
                 deriving ( Eq,Ord,Read,Show)
-- RuleBindings ------------------------------------------------
type RuleBindings = [RuleBinding]
-- Rules -------------------------------------------------------
type Rules = [Rule]
-- SortDecl ----------------------------------------------------
data SortDecl = SortDecl (TypeName) (NameRoots) (CtorDecls)
              deriving ( Eq,Ord,Read,Show)
-- SortDecls ---------------------------------------------------
type SortDecls = [SortDecl]
-- SymbolicTerm ------------------------------------------------
data SymbolicTerm = SymVar (Name)
                  | SymCtorVar (CtorName) (Name)
                  | SymCtorTerm (CtorName) (SymbolicTerms)
                  | SymSubst (Name) (SymbolicTerm) (SymbolicTerm)
                  deriving ( Eq,Ord,Read,Show)
-- SymbolicTerms -----------------------------------------------
type SymbolicTerms = [SymbolicTerm]
-- TermSpec ----------------------------------------------------
data TermSpec = TermSpec (NamespaceDecls) (SortDecls) (FunDecls) (EnvDecls) (RelationDecls)
              deriving ( Eq,Ord,Read,Show)
-- TypeName ----------------------------------------------------
data TypeName = TN (String)
              deriving ( Eq,Ord,Read,Show)
-- TypeNames ---------------------------------------------------
type TypeNames = [TypeName]
-- Vle ---------------------------------------------------------
type Vle = [VleItem]
-- VleItem -----------------------------------------------------
data VleItem = VleBinding (Name)
             | VleCall (FunName) (Name)
             deriving ( Eq,Ord,Read,Show)