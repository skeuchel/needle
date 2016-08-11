

-- UUAGC 0.9.52.1 (src/Coq/Syntax.ag)
module Coq.Syntax( module Coq.Syntax.Core
  , module Coq.Syntax
  ) where

{-# LINE 10 "src/Coq/Syntax.ag" #-}

import Coq.Syntax.Core
{-# LINE 12 "src/Coq/Syntax.hs" #-}
-- Annotation --------------------------------------------------
data Annotation = Struct (Identifier)
                deriving ( Eq,Ord,Show)
-- Assertion ---------------------------------------------------
data Assertion = Assertion (AssertionKeyword) (Identifier) (Binders) (Term)
               deriving ( Eq,Ord,Show)
-- AssertionKeyword --------------------------------------------
data AssertionKeyword = AssTheorem
                      | AssLemma
                      | AssRemark
                      | AssFact
                      | AssCorollary
                      | AssProposition
                      | AssDefinition
                      | AssExample
                      deriving ( Eq,Ord,Show)
-- Binder ------------------------------------------------------
data Binder = BinderName (Name)
            | BinderNameType (Names) (Term)
            | BinderImplicitName (Name)
            | BinderImplicitNameType (Names) (Term)
            deriving ( Eq,Ord,Show)
-- Binders -----------------------------------------------------
type Binders = [Binder]
-- ClassDeclaration --------------------------------------------
data ClassDeclaration = ClassDeclaration (Identifier) (Binders) (MbSort) (MethodDeclarations)
                      deriving ( Eq,Ord,Show)
-- ClassInstance -----------------------------------------------
data ClassInstance = ClassInstance (Identifier) (Binders) (Identifier) (Terms) (Methods)
                   deriving ( Eq,Ord,Show)
-- ContextHyp --------------------------------------------------
data ContextHyp = ContextHyp (Identifier) (Pattern)
                deriving ( Eq,Ord,Show)
-- ContextHyps -------------------------------------------------
type ContextHyps = [ContextHyp]
-- ContextRule -------------------------------------------------
data ContextRule = ContextRule (ContextHyps) (Pattern) (ProofStep)
                 deriving ( Eq,Ord,Show)
-- ContextRules ------------------------------------------------
type ContextRules = [ContextRule]
-- Definition --------------------------------------------------
data Definition = Definition (Identifier) (Binders) (MbTerm) (Term)
                deriving ( Eq,Ord,Show)
-- Equation ----------------------------------------------------
data Equation = Equation (Pattern) (Term)
              deriving ( Eq,Ord,Show)
-- Equations ---------------------------------------------------
type Equations = [Equation]
-- Fixpoint ----------------------------------------------------
data Fixpoint = Fixpoint (FixpointBodies)
              deriving ( Eq,Ord,Show)
-- FixpointBodies ----------------------------------------------
type FixpointBodies = [FixpointBody]
-- FixpointBody ------------------------------------------------
data FixpointBody = FixpointBody (Identifier) (Binders) (MbAnnotation) (Term) (Term)
                  deriving ( Eq,Ord,Show)
-- Hint --------------------------------------------------------
data Hint = HintResolve (Terms)
          | HintRewrite (Terms)
          | HintRewriteRightToLeft (Terms)
          | HintConstructors (Identifiers)
          | HintExtern (Int) (MbPattern) (ProofStep)
          deriving ( Eq,Ord,Show)
-- Identifiers -------------------------------------------------
type Identifiers = [(Identifier)]
-- Inductive ---------------------------------------------------
data Inductive = Inductive (InductiveBodies)
               deriving ( Eq,Ord,Show)
-- InductiveBodies ---------------------------------------------
type InductiveBodies = [InductiveBody]
-- InductiveBody -----------------------------------------------
data InductiveBody = InductiveBody (Identifier) (Binders) (Term) (InductiveCtors)
                   deriving ( Eq,Ord,Show)
-- InductiveCtor -----------------------------------------------
data InductiveCtor = InductiveCtor (Identifier) (Binders) (MbTerm)
                   deriving ( Eq,Ord,Show)
-- InductiveCtors ----------------------------------------------
type InductiveCtors = [InductiveCtor]
-- MatchItem ---------------------------------------------------
data MatchItem = MatchItem (Term) (MbName) (MbTerm)
               deriving ( Eq,Ord,Show)
-- MbAnnotation ------------------------------------------------
type MbAnnotation = Maybe (Annotation)
-- MbName ------------------------------------------------------
type MbName = Maybe (Name)
-- MbPattern ---------------------------------------------------
type MbPattern = Maybe (Pattern)
-- MbSort ------------------------------------------------------
type MbSort = Maybe (Sort)
-- MbTerm ------------------------------------------------------
type MbTerm = Maybe (Term)
-- Method ------------------------------------------------------
data Method = Method (Identifier) (Identifiers) (Term)
            deriving ( Eq,Ord,Show)
-- MethodDeclaration -------------------------------------------
data MethodDeclaration = MethodDeclaration (Identifier) (Binders) (Term)
                       deriving ( Eq,Ord,Show)
-- MethodDeclarations ------------------------------------------
type MethodDeclarations = [MethodDeclaration]
-- Methods -----------------------------------------------------
type Methods = [Method]
-- Modifier ----------------------------------------------------
data Modifier = ModNone
              | ModLocal
              | ModGlobal
              deriving ( Eq,Ord,Show)
-- Name --------------------------------------------------------
data Name = NameIdent (Identifier)
          | NameUnderscore
          deriving ( Eq,Ord,Show)
-- Names -------------------------------------------------------
type Names = [Name]
-- Pattern -----------------------------------------------------
data Pattern = PatCtor (QualId) (Identifiers)
             | PatCtorEx (QualId) (Patterns)
             | PatAtCtor (QualId) (Identifiers)
             | PatAtCtorEx (QualId) (Patterns)
             | PatQualId (QualId)
             | PatUnderscore
             deriving ( Eq,Ord,Show)
-- Patterns ----------------------------------------------------
type Patterns = [Pattern]
-- PossiblyBracketedName ---------------------------------------
data PossiblyBracketedName = BracketedName (Name)
                           | BracedName (Name)
                           | NormalName (Name)
                           deriving ( Eq,Ord,Show)
-- PossiblyBracketedNames --------------------------------------
type PossiblyBracketedNames = [PossiblyBracketedName]
-- Proof -------------------------------------------------------
data Proof = ProofWith (ProofSteps) (ProofSteps)
           | ProofDefined (ProofSteps)
           | ProofQed (ProofSteps)
           deriving ( Eq,Ord,Show)
-- ProofStep ---------------------------------------------------
data ProofStep = PrInduction (Identifier)
               | PrMutualInduction (Identifier) (Int)
               | PrCrushInd
               | PrApply (Term)
               | PrApplyIn (Term) (Identifier)
               | PrExact (Term)
               | PrSeq (ProofSteps)
               | PrIntros (Identifiers)
               | PrRevert (Identifiers)
               | PrTry (ProofStep)
               | PrConstructor
               | PrAuto
               | PrFail
               | PrInversion (Identifier)
               | PrSubst
               | PrSimpl
               | PrRepeat (ProofStep)
               | PrRewrite (Term)
               | PrRewriter
               | PrEasy
               | PrTactic (String) (Terms)
               | PrPoseProof (Term)
               | PrPoseProofAs (Term) (Identifier)
               | PrBullet (Int) (ProofSteps)
               | PrDestruct (Term)
               | PrFEqual (Int) (Term)
               | PrReflexivity
               | PrClear (Identifiers)
               | PrMatchGoal (ContextRules)
               deriving ( Eq,Ord,Show)
-- ProofSteps --------------------------------------------------
type ProofSteps = [ProofStep]
-- QualId ------------------------------------------------------
data QualId = Ident (Identifier)
            deriving ( Eq,Ord,Show)
-- Root --------------------------------------------------------
data Root = Root (Sentences)
          deriving ( Eq,Ord,Show)
-- Scheme ------------------------------------------------------
data Scheme = Scheme (SchemeBodies)
            deriving ( Eq,Ord,Show)
-- SchemeBodies ------------------------------------------------
type SchemeBodies = [SchemeBody]
-- SchemeBody --------------------------------------------------
data SchemeBody = SchemeInduction (Identifier) (Identifier)
                deriving ( Eq,Ord,Show)
-- Sentence ----------------------------------------------------
data Sentence = SentenceDefinition (Definition)
              | SentenceInductive (Inductive)
              | SentenceFixpoint (Fixpoint)
              | SentenceAssertionProof (Assertion) (Proof)
              | SentenceSection (Identifier) (Sentences)
              | SentenceOpaque (Identifier)
              | SentenceHint (Modifier) (Hint) (Identifiers)
              | SentenceScheme (Scheme)
              | SentenceCombinedScheme (Identifier) (Identifiers)
              | SentenceBlankline
              | SentenceArguments (Modifier) (QualId) (PossiblyBracketedNames)
              | SentenceClassDecl (ClassDeclaration)
              | SentenceClassInst (ClassInstance)
              | SentenceVerbatim (String)
              | SentenceContext (Binders)
              deriving ( Eq,Ord,Show)
-- Sentences ---------------------------------------------------
type Sentences = [Sentence]
-- Sort --------------------------------------------------------
data Sort = Prop
          | Set
          | Type
          deriving ( Eq,Ord,Show)
-- Term --------------------------------------------------------
data Term = TermApp (Term) (Terms)
          | TermNum (Int)
          | TermQualId (QualId)
          | TermSort (Sort)
          | TermFunction (Term) (Term)
          | TermAbs (Binders) (Term)
          | TermForall (Binders) (Term)
          | TermAnd (Terms)
          | TermEq (Term) (Term)
          | TermLet (Identifier) (Binders) (MbTerm) (Term) (Term)
          | TermUnderscore
          | TermMatch (MatchItem) (MbTerm) (Equations)
          deriving ( Eq,Ord,Show)
-- Terms -------------------------------------------------------
type Terms = [Term]
-- Variable ----------------------------------------------------
data Variable = Variable (Identifier) (Term)
              deriving ( Eq,Ord,Show)