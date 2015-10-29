

-- UUAGC 0.9.52.1 (src/Coq/AG.ag)
module Coq.AG where
import Coq.Syntax
{-# LINE 10 "src/Coq/Syntax.ag" #-}

import Coq.Syntax.Core
{-# LINE 10 "src/Coq/AG.hs" #-}
{-# LINE 3 "src/Coq/AG.ag" #-}

defaultValues :: Inh_Root
defaultValues = (Inh_Root {})
{-# LINE 15 "src/Coq/AG.hs" #-}
-- Annotation --------------------------------------------------
-- cata
sem_Annotation :: Annotation ->
                  T_Annotation
sem_Annotation (Struct _ident) =
    (sem_Annotation_Struct _ident)
-- semantic domain
type T_Annotation = ( Annotation)
data Inh_Annotation = Inh_Annotation {}
data Syn_Annotation = Syn_Annotation {self_Syn_Annotation :: Annotation}
wrap_Annotation :: T_Annotation ->
                   Inh_Annotation ->
                   Syn_Annotation
wrap_Annotation sem (Inh_Annotation) =
    (let ( _lhsOself) = sem
     in  (Syn_Annotation _lhsOself))
sem_Annotation_Struct :: Identifier ->
                         T_Annotation
sem_Annotation_Struct ident_ =
    (let _lhsOself :: Annotation
         _self =
             Struct ident_
         _lhsOself =
             _self
     in  ( _lhsOself))
-- Assertion ---------------------------------------------------
-- cata
sem_Assertion :: Assertion ->
                 T_Assertion
sem_Assertion (Assertion _assertKeyword _assertIdent _assertBinders _assertType) =
    (sem_Assertion_Assertion (sem_AssertionKeyword _assertKeyword) _assertIdent (sem_Binders _assertBinders) (sem_Term _assertType))
-- semantic domain
type T_Assertion = ( Assertion)
data Inh_Assertion = Inh_Assertion {}
data Syn_Assertion = Syn_Assertion {self_Syn_Assertion :: Assertion}
wrap_Assertion :: T_Assertion ->
                  Inh_Assertion ->
                  Syn_Assertion
wrap_Assertion sem (Inh_Assertion) =
    (let ( _lhsOself) = sem
     in  (Syn_Assertion _lhsOself))
sem_Assertion_Assertion :: T_AssertionKeyword ->
                           Identifier ->
                           T_Binders ->
                           T_Term ->
                           T_Assertion
sem_Assertion_Assertion assertKeyword_ assertIdent_ assertBinders_ assertType_ =
    (let _lhsOself :: Assertion
         _assertKeywordIself :: AssertionKeyword
         _assertBindersIself :: Binders
         _assertTypeIself :: Term
         _self =
             Assertion _assertKeywordIself assertIdent_ _assertBindersIself _assertTypeIself
         _lhsOself =
             _self
         ( _assertKeywordIself) =
             assertKeyword_
         ( _assertBindersIself) =
             assertBinders_
         ( _assertTypeIself) =
             assertType_
     in  ( _lhsOself))
-- AssertionKeyword --------------------------------------------
-- cata
sem_AssertionKeyword :: AssertionKeyword ->
                        T_AssertionKeyword
sem_AssertionKeyword (AssTheorem) =
    (sem_AssertionKeyword_AssTheorem)
sem_AssertionKeyword (AssLemma) =
    (sem_AssertionKeyword_AssLemma)
sem_AssertionKeyword (AssRemark) =
    (sem_AssertionKeyword_AssRemark)
sem_AssertionKeyword (AssFact) =
    (sem_AssertionKeyword_AssFact)
sem_AssertionKeyword (AssCorollary) =
    (sem_AssertionKeyword_AssCorollary)
sem_AssertionKeyword (AssProposition) =
    (sem_AssertionKeyword_AssProposition)
sem_AssertionKeyword (AssDefinition) =
    (sem_AssertionKeyword_AssDefinition)
sem_AssertionKeyword (AssExample) =
    (sem_AssertionKeyword_AssExample)
-- semantic domain
type T_AssertionKeyword = ( AssertionKeyword)
data Inh_AssertionKeyword = Inh_AssertionKeyword {}
data Syn_AssertionKeyword = Syn_AssertionKeyword {self_Syn_AssertionKeyword :: AssertionKeyword}
wrap_AssertionKeyword :: T_AssertionKeyword ->
                         Inh_AssertionKeyword ->
                         Syn_AssertionKeyword
wrap_AssertionKeyword sem (Inh_AssertionKeyword) =
    (let ( _lhsOself) = sem
     in  (Syn_AssertionKeyword _lhsOself))
sem_AssertionKeyword_AssTheorem :: T_AssertionKeyword
sem_AssertionKeyword_AssTheorem =
    (let _lhsOself :: AssertionKeyword
         _self =
             AssTheorem
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_AssertionKeyword_AssLemma :: T_AssertionKeyword
sem_AssertionKeyword_AssLemma =
    (let _lhsOself :: AssertionKeyword
         _self =
             AssLemma
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_AssertionKeyword_AssRemark :: T_AssertionKeyword
sem_AssertionKeyword_AssRemark =
    (let _lhsOself :: AssertionKeyword
         _self =
             AssRemark
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_AssertionKeyword_AssFact :: T_AssertionKeyword
sem_AssertionKeyword_AssFact =
    (let _lhsOself :: AssertionKeyword
         _self =
             AssFact
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_AssertionKeyword_AssCorollary :: T_AssertionKeyword
sem_AssertionKeyword_AssCorollary =
    (let _lhsOself :: AssertionKeyword
         _self =
             AssCorollary
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_AssertionKeyword_AssProposition :: T_AssertionKeyword
sem_AssertionKeyword_AssProposition =
    (let _lhsOself :: AssertionKeyword
         _self =
             AssProposition
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_AssertionKeyword_AssDefinition :: T_AssertionKeyword
sem_AssertionKeyword_AssDefinition =
    (let _lhsOself :: AssertionKeyword
         _self =
             AssDefinition
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_AssertionKeyword_AssExample :: T_AssertionKeyword
sem_AssertionKeyword_AssExample =
    (let _lhsOself :: AssertionKeyword
         _self =
             AssExample
         _lhsOself =
             _self
     in  ( _lhsOself))
-- Binder ------------------------------------------------------
-- cata
sem_Binder :: Binder ->
              T_Binder
sem_Binder (BinderName _binderName) =
    (sem_Binder_BinderName (sem_Name _binderName))
sem_Binder (BinderNameType _binderNames _binderType) =
    (sem_Binder_BinderNameType (sem_Names _binderNames) (sem_Term _binderType))
sem_Binder (BinderImplicitName _binderName) =
    (sem_Binder_BinderImplicitName (sem_Name _binderName))
sem_Binder (BinderImplicitNameType _binderNames _binderType) =
    (sem_Binder_BinderImplicitNameType (sem_Names _binderNames) (sem_Term _binderType))
-- semantic domain
type T_Binder = ( Binder)
data Inh_Binder = Inh_Binder {}
data Syn_Binder = Syn_Binder {self_Syn_Binder :: Binder}
wrap_Binder :: T_Binder ->
               Inh_Binder ->
               Syn_Binder
wrap_Binder sem (Inh_Binder) =
    (let ( _lhsOself) = sem
     in  (Syn_Binder _lhsOself))
sem_Binder_BinderName :: T_Name ->
                         T_Binder
sem_Binder_BinderName binderName_ =
    (let _lhsOself :: Binder
         _binderNameIself :: Name
         _self =
             BinderName _binderNameIself
         _lhsOself =
             _self
         ( _binderNameIself) =
             binderName_
     in  ( _lhsOself))
sem_Binder_BinderNameType :: T_Names ->
                             T_Term ->
                             T_Binder
sem_Binder_BinderNameType binderNames_ binderType_ =
    (let _lhsOself :: Binder
         _binderNamesIself :: Names
         _binderTypeIself :: Term
         _self =
             BinderNameType _binderNamesIself _binderTypeIself
         _lhsOself =
             _self
         ( _binderNamesIself) =
             binderNames_
         ( _binderTypeIself) =
             binderType_
     in  ( _lhsOself))
sem_Binder_BinderImplicitName :: T_Name ->
                                 T_Binder
sem_Binder_BinderImplicitName binderName_ =
    (let _lhsOself :: Binder
         _binderNameIself :: Name
         _self =
             BinderImplicitName _binderNameIself
         _lhsOself =
             _self
         ( _binderNameIself) =
             binderName_
     in  ( _lhsOself))
sem_Binder_BinderImplicitNameType :: T_Names ->
                                     T_Term ->
                                     T_Binder
sem_Binder_BinderImplicitNameType binderNames_ binderType_ =
    (let _lhsOself :: Binder
         _binderNamesIself :: Names
         _binderTypeIself :: Term
         _self =
             BinderImplicitNameType _binderNamesIself _binderTypeIself
         _lhsOself =
             _self
         ( _binderNamesIself) =
             binderNames_
         ( _binderTypeIself) =
             binderType_
     in  ( _lhsOself))
-- Binders -----------------------------------------------------
-- cata
sem_Binders :: Binders ->
               T_Binders
sem_Binders list =
    (Prelude.foldr sem_Binders_Cons sem_Binders_Nil (Prelude.map sem_Binder list))
-- semantic domain
type T_Binders = ( Binders)
data Inh_Binders = Inh_Binders {}
data Syn_Binders = Syn_Binders {self_Syn_Binders :: Binders}
wrap_Binders :: T_Binders ->
                Inh_Binders ->
                Syn_Binders
wrap_Binders sem (Inh_Binders) =
    (let ( _lhsOself) = sem
     in  (Syn_Binders _lhsOself))
sem_Binders_Cons :: T_Binder ->
                    T_Binders ->
                    T_Binders
sem_Binders_Cons hd_ tl_ =
    (let _lhsOself :: Binders
         _hdIself :: Binder
         _tlIself :: Binders
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             hd_
         ( _tlIself) =
             tl_
     in  ( _lhsOself))
sem_Binders_Nil :: T_Binders
sem_Binders_Nil =
    (let _lhsOself :: Binders
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
-- ClassDeclaration --------------------------------------------
-- cata
sem_ClassDeclaration :: ClassDeclaration ->
                        T_ClassDeclaration
sem_ClassDeclaration (ClassDeclaration _className _classParams _classSort _classMethods) =
    (sem_ClassDeclaration_ClassDeclaration _className (sem_Binders _classParams) (sem_MbSort _classSort) (sem_MethodDeclarations _classMethods))
-- semantic domain
type T_ClassDeclaration = ( ClassDeclaration)
data Inh_ClassDeclaration = Inh_ClassDeclaration {}
data Syn_ClassDeclaration = Syn_ClassDeclaration {self_Syn_ClassDeclaration :: ClassDeclaration}
wrap_ClassDeclaration :: T_ClassDeclaration ->
                         Inh_ClassDeclaration ->
                         Syn_ClassDeclaration
wrap_ClassDeclaration sem (Inh_ClassDeclaration) =
    (let ( _lhsOself) = sem
     in  (Syn_ClassDeclaration _lhsOself))
sem_ClassDeclaration_ClassDeclaration :: Identifier ->
                                         T_Binders ->
                                         T_MbSort ->
                                         T_MethodDeclarations ->
                                         T_ClassDeclaration
sem_ClassDeclaration_ClassDeclaration className_ classParams_ classSort_ classMethods_ =
    (let _lhsOself :: ClassDeclaration
         _classParamsIself :: Binders
         _classSortIself :: MbSort
         _classMethodsIself :: MethodDeclarations
         _self =
             ClassDeclaration className_ _classParamsIself _classSortIself _classMethodsIself
         _lhsOself =
             _self
         ( _classParamsIself) =
             classParams_
         ( _classSortIself) =
             classSort_
         ( _classMethodsIself) =
             classMethods_
     in  ( _lhsOself))
-- ClassInstance -----------------------------------------------
-- cata
sem_ClassInstance :: ClassInstance ->
                     T_ClassInstance
sem_ClassInstance (ClassInstance _instName _instBinders _instClass _instParams _instMethods) =
    (sem_ClassInstance_ClassInstance _instName (sem_Binders _instBinders) _instClass (sem_Terms _instParams) (sem_Methods _instMethods))
-- semantic domain
type T_ClassInstance = ( ClassInstance)
data Inh_ClassInstance = Inh_ClassInstance {}
data Syn_ClassInstance = Syn_ClassInstance {self_Syn_ClassInstance :: ClassInstance}
wrap_ClassInstance :: T_ClassInstance ->
                      Inh_ClassInstance ->
                      Syn_ClassInstance
wrap_ClassInstance sem (Inh_ClassInstance) =
    (let ( _lhsOself) = sem
     in  (Syn_ClassInstance _lhsOself))
sem_ClassInstance_ClassInstance :: Identifier ->
                                   T_Binders ->
                                   Identifier ->
                                   T_Terms ->
                                   T_Methods ->
                                   T_ClassInstance
sem_ClassInstance_ClassInstance instName_ instBinders_ instClass_ instParams_ instMethods_ =
    (let _lhsOself :: ClassInstance
         _instBindersIself :: Binders
         _instParamsIself :: Terms
         _instMethodsIself :: Methods
         _self =
             ClassInstance instName_ _instBindersIself instClass_ _instParamsIself _instMethodsIself
         _lhsOself =
             _self
         ( _instBindersIself) =
             instBinders_
         ( _instParamsIself) =
             instParams_
         ( _instMethodsIself) =
             instMethods_
     in  ( _lhsOself))
-- ContextHyp --------------------------------------------------
-- cata
sem_ContextHyp :: ContextHyp ->
                  T_ContextHyp
sem_ContextHyp (ContextHyp _ident _pattern) =
    (sem_ContextHyp_ContextHyp _ident (sem_Pattern _pattern))
-- semantic domain
type T_ContextHyp = ( ContextHyp)
data Inh_ContextHyp = Inh_ContextHyp {}
data Syn_ContextHyp = Syn_ContextHyp {self_Syn_ContextHyp :: ContextHyp}
wrap_ContextHyp :: T_ContextHyp ->
                   Inh_ContextHyp ->
                   Syn_ContextHyp
wrap_ContextHyp sem (Inh_ContextHyp) =
    (let ( _lhsOself) = sem
     in  (Syn_ContextHyp _lhsOself))
sem_ContextHyp_ContextHyp :: Identifier ->
                             T_Pattern ->
                             T_ContextHyp
sem_ContextHyp_ContextHyp ident_ pattern_ =
    (let _lhsOself :: ContextHyp
         _patternIself :: Pattern
         _self =
             ContextHyp ident_ _patternIself
         _lhsOself =
             _self
         ( _patternIself) =
             pattern_
     in  ( _lhsOself))
-- ContextHyps -------------------------------------------------
-- cata
sem_ContextHyps :: ContextHyps ->
                   T_ContextHyps
sem_ContextHyps list =
    (Prelude.foldr sem_ContextHyps_Cons sem_ContextHyps_Nil (Prelude.map sem_ContextHyp list))
-- semantic domain
type T_ContextHyps = ( ContextHyps)
data Inh_ContextHyps = Inh_ContextHyps {}
data Syn_ContextHyps = Syn_ContextHyps {self_Syn_ContextHyps :: ContextHyps}
wrap_ContextHyps :: T_ContextHyps ->
                    Inh_ContextHyps ->
                    Syn_ContextHyps
wrap_ContextHyps sem (Inh_ContextHyps) =
    (let ( _lhsOself) = sem
     in  (Syn_ContextHyps _lhsOself))
sem_ContextHyps_Cons :: T_ContextHyp ->
                        T_ContextHyps ->
                        T_ContextHyps
sem_ContextHyps_Cons hd_ tl_ =
    (let _lhsOself :: ContextHyps
         _hdIself :: ContextHyp
         _tlIself :: ContextHyps
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             hd_
         ( _tlIself) =
             tl_
     in  ( _lhsOself))
sem_ContextHyps_Nil :: T_ContextHyps
sem_ContextHyps_Nil =
    (let _lhsOself :: ContextHyps
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
-- ContextRule -------------------------------------------------
-- cata
sem_ContextRule :: ContextRule ->
                   T_ContextRule
sem_ContextRule (ContextRule _hypotheses _goal _tactic) =
    (sem_ContextRule_ContextRule (sem_ContextHyps _hypotheses) (sem_Pattern _goal) (sem_ProofStep _tactic))
-- semantic domain
type T_ContextRule = ( ContextRule)
data Inh_ContextRule = Inh_ContextRule {}
data Syn_ContextRule = Syn_ContextRule {self_Syn_ContextRule :: ContextRule}
wrap_ContextRule :: T_ContextRule ->
                    Inh_ContextRule ->
                    Syn_ContextRule
wrap_ContextRule sem (Inh_ContextRule) =
    (let ( _lhsOself) = sem
     in  (Syn_ContextRule _lhsOself))
sem_ContextRule_ContextRule :: T_ContextHyps ->
                               T_Pattern ->
                               T_ProofStep ->
                               T_ContextRule
sem_ContextRule_ContextRule hypotheses_ goal_ tactic_ =
    (let _lhsOself :: ContextRule
         _hypothesesIself :: ContextHyps
         _goalIself :: Pattern
         _tacticIself :: ProofStep
         _self =
             ContextRule _hypothesesIself _goalIself _tacticIself
         _lhsOself =
             _self
         ( _hypothesesIself) =
             hypotheses_
         ( _goalIself) =
             goal_
         ( _tacticIself) =
             tactic_
     in  ( _lhsOself))
-- ContextRules ------------------------------------------------
-- cata
sem_ContextRules :: ContextRules ->
                    T_ContextRules
sem_ContextRules list =
    (Prelude.foldr sem_ContextRules_Cons sem_ContextRules_Nil (Prelude.map sem_ContextRule list))
-- semantic domain
type T_ContextRules = ( ContextRules)
data Inh_ContextRules = Inh_ContextRules {}
data Syn_ContextRules = Syn_ContextRules {self_Syn_ContextRules :: ContextRules}
wrap_ContextRules :: T_ContextRules ->
                     Inh_ContextRules ->
                     Syn_ContextRules
wrap_ContextRules sem (Inh_ContextRules) =
    (let ( _lhsOself) = sem
     in  (Syn_ContextRules _lhsOself))
sem_ContextRules_Cons :: T_ContextRule ->
                         T_ContextRules ->
                         T_ContextRules
sem_ContextRules_Cons hd_ tl_ =
    (let _lhsOself :: ContextRules
         _hdIself :: ContextRule
         _tlIself :: ContextRules
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             hd_
         ( _tlIself) =
             tl_
     in  ( _lhsOself))
sem_ContextRules_Nil :: T_ContextRules
sem_ContextRules_Nil =
    (let _lhsOself :: ContextRules
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
-- Definition --------------------------------------------------
-- cata
sem_Definition :: Definition ->
                  T_Definition
sem_Definition (Definition _defIdent _defBinders _defType _defExpr) =
    (sem_Definition_Definition _defIdent (sem_Binders _defBinders) (sem_MbTerm _defType) (sem_Term _defExpr))
-- semantic domain
type T_Definition = ( Definition)
data Inh_Definition = Inh_Definition {}
data Syn_Definition = Syn_Definition {self_Syn_Definition :: Definition}
wrap_Definition :: T_Definition ->
                   Inh_Definition ->
                   Syn_Definition
wrap_Definition sem (Inh_Definition) =
    (let ( _lhsOself) = sem
     in  (Syn_Definition _lhsOself))
sem_Definition_Definition :: Identifier ->
                             T_Binders ->
                             T_MbTerm ->
                             T_Term ->
                             T_Definition
sem_Definition_Definition defIdent_ defBinders_ defType_ defExpr_ =
    (let _lhsOself :: Definition
         _defBindersIself :: Binders
         _defTypeIself :: MbTerm
         _defExprIself :: Term
         _self =
             Definition defIdent_ _defBindersIself _defTypeIself _defExprIself
         _lhsOself =
             _self
         ( _defBindersIself) =
             defBinders_
         ( _defTypeIself) =
             defType_
         ( _defExprIself) =
             defExpr_
     in  ( _lhsOself))
-- Equation ----------------------------------------------------
-- cata
sem_Equation :: Equation ->
                T_Equation
sem_Equation (Equation _eqPattern _eqBody) =
    (sem_Equation_Equation (sem_Pattern _eqPattern) (sem_Term _eqBody))
-- semantic domain
type T_Equation = ( Equation)
data Inh_Equation = Inh_Equation {}
data Syn_Equation = Syn_Equation {self_Syn_Equation :: Equation}
wrap_Equation :: T_Equation ->
                 Inh_Equation ->
                 Syn_Equation
wrap_Equation sem (Inh_Equation) =
    (let ( _lhsOself) = sem
     in  (Syn_Equation _lhsOself))
sem_Equation_Equation :: T_Pattern ->
                         T_Term ->
                         T_Equation
sem_Equation_Equation eqPattern_ eqBody_ =
    (let _lhsOself :: Equation
         _eqPatternIself :: Pattern
         _eqBodyIself :: Term
         _self =
             Equation _eqPatternIself _eqBodyIself
         _lhsOself =
             _self
         ( _eqPatternIself) =
             eqPattern_
         ( _eqBodyIself) =
             eqBody_
     in  ( _lhsOself))
-- Equations ---------------------------------------------------
-- cata
sem_Equations :: Equations ->
                 T_Equations
sem_Equations list =
    (Prelude.foldr sem_Equations_Cons sem_Equations_Nil (Prelude.map sem_Equation list))
-- semantic domain
type T_Equations = ( Equations)
data Inh_Equations = Inh_Equations {}
data Syn_Equations = Syn_Equations {self_Syn_Equations :: Equations}
wrap_Equations :: T_Equations ->
                  Inh_Equations ->
                  Syn_Equations
wrap_Equations sem (Inh_Equations) =
    (let ( _lhsOself) = sem
     in  (Syn_Equations _lhsOself))
sem_Equations_Cons :: T_Equation ->
                      T_Equations ->
                      T_Equations
sem_Equations_Cons hd_ tl_ =
    (let _lhsOself :: Equations
         _hdIself :: Equation
         _tlIself :: Equations
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             hd_
         ( _tlIself) =
             tl_
     in  ( _lhsOself))
sem_Equations_Nil :: T_Equations
sem_Equations_Nil =
    (let _lhsOself :: Equations
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
-- Fixpoint ----------------------------------------------------
-- cata
sem_Fixpoint :: Fixpoint ->
                T_Fixpoint
sem_Fixpoint (Fixpoint _bodies) =
    (sem_Fixpoint_Fixpoint (sem_FixpointBodies _bodies))
-- semantic domain
type T_Fixpoint = ( Fixpoint)
data Inh_Fixpoint = Inh_Fixpoint {}
data Syn_Fixpoint = Syn_Fixpoint {self_Syn_Fixpoint :: Fixpoint}
wrap_Fixpoint :: T_Fixpoint ->
                 Inh_Fixpoint ->
                 Syn_Fixpoint
wrap_Fixpoint sem (Inh_Fixpoint) =
    (let ( _lhsOself) = sem
     in  (Syn_Fixpoint _lhsOself))
sem_Fixpoint_Fixpoint :: T_FixpointBodies ->
                         T_Fixpoint
sem_Fixpoint_Fixpoint bodies_ =
    (let _lhsOself :: Fixpoint
         _bodiesIself :: FixpointBodies
         _self =
             Fixpoint _bodiesIself
         _lhsOself =
             _self
         ( _bodiesIself) =
             bodies_
     in  ( _lhsOself))
-- FixpointBodies ----------------------------------------------
-- cata
sem_FixpointBodies :: FixpointBodies ->
                      T_FixpointBodies
sem_FixpointBodies list =
    (Prelude.foldr sem_FixpointBodies_Cons sem_FixpointBodies_Nil (Prelude.map sem_FixpointBody list))
-- semantic domain
type T_FixpointBodies = ( FixpointBodies)
data Inh_FixpointBodies = Inh_FixpointBodies {}
data Syn_FixpointBodies = Syn_FixpointBodies {self_Syn_FixpointBodies :: FixpointBodies}
wrap_FixpointBodies :: T_FixpointBodies ->
                       Inh_FixpointBodies ->
                       Syn_FixpointBodies
wrap_FixpointBodies sem (Inh_FixpointBodies) =
    (let ( _lhsOself) = sem
     in  (Syn_FixpointBodies _lhsOself))
sem_FixpointBodies_Cons :: T_FixpointBody ->
                           T_FixpointBodies ->
                           T_FixpointBodies
sem_FixpointBodies_Cons hd_ tl_ =
    (let _lhsOself :: FixpointBodies
         _hdIself :: FixpointBody
         _tlIself :: FixpointBodies
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             hd_
         ( _tlIself) =
             tl_
     in  ( _lhsOself))
sem_FixpointBodies_Nil :: T_FixpointBodies
sem_FixpointBodies_Nil =
    (let _lhsOself :: FixpointBodies
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
-- FixpointBody ------------------------------------------------
-- cata
sem_FixpointBody :: FixpointBody ->
                    T_FixpointBody
sem_FixpointBody (FixpointBody _fixIdent _fixBinders _fixAnno _fixType _fixExpr) =
    (sem_FixpointBody_FixpointBody _fixIdent (sem_Binders _fixBinders) (sem_MbAnnotation _fixAnno) (sem_Term _fixType) (sem_Term _fixExpr))
-- semantic domain
type T_FixpointBody = ( FixpointBody)
data Inh_FixpointBody = Inh_FixpointBody {}
data Syn_FixpointBody = Syn_FixpointBody {self_Syn_FixpointBody :: FixpointBody}
wrap_FixpointBody :: T_FixpointBody ->
                     Inh_FixpointBody ->
                     Syn_FixpointBody
wrap_FixpointBody sem (Inh_FixpointBody) =
    (let ( _lhsOself) = sem
     in  (Syn_FixpointBody _lhsOself))
sem_FixpointBody_FixpointBody :: Identifier ->
                                 T_Binders ->
                                 T_MbAnnotation ->
                                 T_Term ->
                                 T_Term ->
                                 T_FixpointBody
sem_FixpointBody_FixpointBody fixIdent_ fixBinders_ fixAnno_ fixType_ fixExpr_ =
    (let _lhsOself :: FixpointBody
         _fixBindersIself :: Binders
         _fixAnnoIself :: MbAnnotation
         _fixTypeIself :: Term
         _fixExprIself :: Term
         _self =
             FixpointBody fixIdent_ _fixBindersIself _fixAnnoIself _fixTypeIself _fixExprIself
         _lhsOself =
             _self
         ( _fixBindersIself) =
             fixBinders_
         ( _fixAnnoIself) =
             fixAnno_
         ( _fixTypeIself) =
             fixType_
         ( _fixExprIself) =
             fixExpr_
     in  ( _lhsOself))
-- Hint --------------------------------------------------------
-- cata
sem_Hint :: Hint ->
            T_Hint
sem_Hint (HintResolve _hints) =
    (sem_Hint_HintResolve (sem_Terms _hints))
sem_Hint (HintRewrite _hints) =
    (sem_Hint_HintRewrite (sem_Terms _hints))
sem_Hint (HintConstructors _ids) =
    (sem_Hint_HintConstructors (sem_Identifiers _ids))
sem_Hint (HintExtern _level _pattern _tactic) =
    (sem_Hint_HintExtern _level (sem_MbPattern _pattern) (sem_ProofStep _tactic))
-- semantic domain
type T_Hint = ( Hint)
data Inh_Hint = Inh_Hint {}
data Syn_Hint = Syn_Hint {self_Syn_Hint :: Hint}
wrap_Hint :: T_Hint ->
             Inh_Hint ->
             Syn_Hint
wrap_Hint sem (Inh_Hint) =
    (let ( _lhsOself) = sem
     in  (Syn_Hint _lhsOself))
sem_Hint_HintResolve :: T_Terms ->
                        T_Hint
sem_Hint_HintResolve hints_ =
    (let _lhsOself :: Hint
         _hintsIself :: Terms
         _self =
             HintResolve _hintsIself
         _lhsOself =
             _self
         ( _hintsIself) =
             hints_
     in  ( _lhsOself))
sem_Hint_HintRewrite :: T_Terms ->
                        T_Hint
sem_Hint_HintRewrite hints_ =
    (let _lhsOself :: Hint
         _hintsIself :: Terms
         _self =
             HintRewrite _hintsIself
         _lhsOself =
             _self
         ( _hintsIself) =
             hints_
     in  ( _lhsOself))
sem_Hint_HintConstructors :: T_Identifiers ->
                             T_Hint
sem_Hint_HintConstructors ids_ =
    (let _lhsOself :: Hint
         _idsIself :: Identifiers
         _self =
             HintConstructors _idsIself
         _lhsOself =
             _self
         ( _idsIself) =
             ids_
     in  ( _lhsOself))
sem_Hint_HintExtern :: Int ->
                       T_MbPattern ->
                       T_ProofStep ->
                       T_Hint
sem_Hint_HintExtern level_ pattern_ tactic_ =
    (let _lhsOself :: Hint
         _patternIself :: MbPattern
         _tacticIself :: ProofStep
         _self =
             HintExtern level_ _patternIself _tacticIself
         _lhsOself =
             _self
         ( _patternIself) =
             pattern_
         ( _tacticIself) =
             tactic_
     in  ( _lhsOself))
-- Identifiers -------------------------------------------------
-- cata
sem_Identifiers :: Identifiers ->
                   T_Identifiers
sem_Identifiers list =
    (Prelude.foldr sem_Identifiers_Cons sem_Identifiers_Nil list)
-- semantic domain
type T_Identifiers = ( Identifiers)
data Inh_Identifiers = Inh_Identifiers {}
data Syn_Identifiers = Syn_Identifiers {self_Syn_Identifiers :: Identifiers}
wrap_Identifiers :: T_Identifiers ->
                    Inh_Identifiers ->
                    Syn_Identifiers
wrap_Identifiers sem (Inh_Identifiers) =
    (let ( _lhsOself) = sem
     in  (Syn_Identifiers _lhsOself))
sem_Identifiers_Cons :: Identifier ->
                        T_Identifiers ->
                        T_Identifiers
sem_Identifiers_Cons hd_ tl_ =
    (let _lhsOself :: Identifiers
         _tlIself :: Identifiers
         _self =
             (:) hd_ _tlIself
         _lhsOself =
             _self
         ( _tlIself) =
             tl_
     in  ( _lhsOself))
sem_Identifiers_Nil :: T_Identifiers
sem_Identifiers_Nil =
    (let _lhsOself :: Identifiers
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
-- Inductive ---------------------------------------------------
-- cata
sem_Inductive :: Inductive ->
                 T_Inductive
sem_Inductive (Inductive _bodies) =
    (sem_Inductive_Inductive (sem_InductiveBodies _bodies))
-- semantic domain
type T_Inductive = ( Inductive)
data Inh_Inductive = Inh_Inductive {}
data Syn_Inductive = Syn_Inductive {self_Syn_Inductive :: Inductive}
wrap_Inductive :: T_Inductive ->
                  Inh_Inductive ->
                  Syn_Inductive
wrap_Inductive sem (Inh_Inductive) =
    (let ( _lhsOself) = sem
     in  (Syn_Inductive _lhsOself))
sem_Inductive_Inductive :: T_InductiveBodies ->
                           T_Inductive
sem_Inductive_Inductive bodies_ =
    (let _lhsOself :: Inductive
         _bodiesIself :: InductiveBodies
         _self =
             Inductive _bodiesIself
         _lhsOself =
             _self
         ( _bodiesIself) =
             bodies_
     in  ( _lhsOself))
-- InductiveBodies ---------------------------------------------
-- cata
sem_InductiveBodies :: InductiveBodies ->
                       T_InductiveBodies
sem_InductiveBodies list =
    (Prelude.foldr sem_InductiveBodies_Cons sem_InductiveBodies_Nil (Prelude.map sem_InductiveBody list))
-- semantic domain
type T_InductiveBodies = ( InductiveBodies)
data Inh_InductiveBodies = Inh_InductiveBodies {}
data Syn_InductiveBodies = Syn_InductiveBodies {self_Syn_InductiveBodies :: InductiveBodies}
wrap_InductiveBodies :: T_InductiveBodies ->
                        Inh_InductiveBodies ->
                        Syn_InductiveBodies
wrap_InductiveBodies sem (Inh_InductiveBodies) =
    (let ( _lhsOself) = sem
     in  (Syn_InductiveBodies _lhsOself))
sem_InductiveBodies_Cons :: T_InductiveBody ->
                            T_InductiveBodies ->
                            T_InductiveBodies
sem_InductiveBodies_Cons hd_ tl_ =
    (let _lhsOself :: InductiveBodies
         _hdIself :: InductiveBody
         _tlIself :: InductiveBodies
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             hd_
         ( _tlIself) =
             tl_
     in  ( _lhsOself))
sem_InductiveBodies_Nil :: T_InductiveBodies
sem_InductiveBodies_Nil =
    (let _lhsOself :: InductiveBodies
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
-- InductiveBody -----------------------------------------------
-- cata
sem_InductiveBody :: InductiveBody ->
                     T_InductiveBody
sem_InductiveBody (InductiveBody _indIdent _indBinders _indType _indCtors) =
    (sem_InductiveBody_InductiveBody _indIdent (sem_Binders _indBinders) (sem_Term _indType) (sem_InductiveCtors _indCtors))
-- semantic domain
type T_InductiveBody = ( InductiveBody)
data Inh_InductiveBody = Inh_InductiveBody {}
data Syn_InductiveBody = Syn_InductiveBody {self_Syn_InductiveBody :: InductiveBody}
wrap_InductiveBody :: T_InductiveBody ->
                      Inh_InductiveBody ->
                      Syn_InductiveBody
wrap_InductiveBody sem (Inh_InductiveBody) =
    (let ( _lhsOself) = sem
     in  (Syn_InductiveBody _lhsOself))
sem_InductiveBody_InductiveBody :: Identifier ->
                                   T_Binders ->
                                   T_Term ->
                                   T_InductiveCtors ->
                                   T_InductiveBody
sem_InductiveBody_InductiveBody indIdent_ indBinders_ indType_ indCtors_ =
    (let _lhsOself :: InductiveBody
         _indBindersIself :: Binders
         _indTypeIself :: Term
         _indCtorsIself :: InductiveCtors
         _self =
             InductiveBody indIdent_ _indBindersIself _indTypeIself _indCtorsIself
         _lhsOself =
             _self
         ( _indBindersIself) =
             indBinders_
         ( _indTypeIself) =
             indType_
         ( _indCtorsIself) =
             indCtors_
     in  ( _lhsOself))
-- InductiveCtor -----------------------------------------------
-- cata
sem_InductiveCtor :: InductiveCtor ->
                     T_InductiveCtor
sem_InductiveCtor (InductiveCtor _ctorIdent _ctorBinders _ctorType) =
    (sem_InductiveCtor_InductiveCtor _ctorIdent (sem_Binders _ctorBinders) (sem_MbTerm _ctorType))
-- semantic domain
type T_InductiveCtor = ( InductiveCtor)
data Inh_InductiveCtor = Inh_InductiveCtor {}
data Syn_InductiveCtor = Syn_InductiveCtor {self_Syn_InductiveCtor :: InductiveCtor}
wrap_InductiveCtor :: T_InductiveCtor ->
                      Inh_InductiveCtor ->
                      Syn_InductiveCtor
wrap_InductiveCtor sem (Inh_InductiveCtor) =
    (let ( _lhsOself) = sem
     in  (Syn_InductiveCtor _lhsOself))
sem_InductiveCtor_InductiveCtor :: Identifier ->
                                   T_Binders ->
                                   T_MbTerm ->
                                   T_InductiveCtor
sem_InductiveCtor_InductiveCtor ctorIdent_ ctorBinders_ ctorType_ =
    (let _lhsOself :: InductiveCtor
         _ctorBindersIself :: Binders
         _ctorTypeIself :: MbTerm
         _self =
             InductiveCtor ctorIdent_ _ctorBindersIself _ctorTypeIself
         _lhsOself =
             _self
         ( _ctorBindersIself) =
             ctorBinders_
         ( _ctorTypeIself) =
             ctorType_
     in  ( _lhsOself))
-- InductiveCtors ----------------------------------------------
-- cata
sem_InductiveCtors :: InductiveCtors ->
                      T_InductiveCtors
sem_InductiveCtors list =
    (Prelude.foldr sem_InductiveCtors_Cons sem_InductiveCtors_Nil (Prelude.map sem_InductiveCtor list))
-- semantic domain
type T_InductiveCtors = ( InductiveCtors)
data Inh_InductiveCtors = Inh_InductiveCtors {}
data Syn_InductiveCtors = Syn_InductiveCtors {self_Syn_InductiveCtors :: InductiveCtors}
wrap_InductiveCtors :: T_InductiveCtors ->
                       Inh_InductiveCtors ->
                       Syn_InductiveCtors
wrap_InductiveCtors sem (Inh_InductiveCtors) =
    (let ( _lhsOself) = sem
     in  (Syn_InductiveCtors _lhsOself))
sem_InductiveCtors_Cons :: T_InductiveCtor ->
                           T_InductiveCtors ->
                           T_InductiveCtors
sem_InductiveCtors_Cons hd_ tl_ =
    (let _lhsOself :: InductiveCtors
         _hdIself :: InductiveCtor
         _tlIself :: InductiveCtors
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             hd_
         ( _tlIself) =
             tl_
     in  ( _lhsOself))
sem_InductiveCtors_Nil :: T_InductiveCtors
sem_InductiveCtors_Nil =
    (let _lhsOself :: InductiveCtors
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
-- MatchItem ---------------------------------------------------
-- cata
sem_MatchItem :: MatchItem ->
                 T_MatchItem
sem_MatchItem (MatchItem _matchItemTerm _matchItemAs _matchItemIn) =
    (sem_MatchItem_MatchItem (sem_Term _matchItemTerm) (sem_MbName _matchItemAs) (sem_MbTerm _matchItemIn))
-- semantic domain
type T_MatchItem = ( MatchItem)
data Inh_MatchItem = Inh_MatchItem {}
data Syn_MatchItem = Syn_MatchItem {self_Syn_MatchItem :: MatchItem}
wrap_MatchItem :: T_MatchItem ->
                  Inh_MatchItem ->
                  Syn_MatchItem
wrap_MatchItem sem (Inh_MatchItem) =
    (let ( _lhsOself) = sem
     in  (Syn_MatchItem _lhsOself))
sem_MatchItem_MatchItem :: T_Term ->
                           T_MbName ->
                           T_MbTerm ->
                           T_MatchItem
sem_MatchItem_MatchItem matchItemTerm_ matchItemAs_ matchItemIn_ =
    (let _lhsOself :: MatchItem
         _matchItemTermIself :: Term
         _matchItemAsIself :: MbName
         _matchItemInIself :: MbTerm
         _self =
             MatchItem _matchItemTermIself _matchItemAsIself _matchItemInIself
         _lhsOself =
             _self
         ( _matchItemTermIself) =
             matchItemTerm_
         ( _matchItemAsIself) =
             matchItemAs_
         ( _matchItemInIself) =
             matchItemIn_
     in  ( _lhsOself))
-- MbAnnotation ------------------------------------------------
-- cata
sem_MbAnnotation :: MbAnnotation ->
                    T_MbAnnotation
sem_MbAnnotation (Prelude.Just x) =
    (sem_MbAnnotation_Just (sem_Annotation x))
sem_MbAnnotation Prelude.Nothing =
    sem_MbAnnotation_Nothing
-- semantic domain
type T_MbAnnotation = ( MbAnnotation)
data Inh_MbAnnotation = Inh_MbAnnotation {}
data Syn_MbAnnotation = Syn_MbAnnotation {self_Syn_MbAnnotation :: MbAnnotation}
wrap_MbAnnotation :: T_MbAnnotation ->
                     Inh_MbAnnotation ->
                     Syn_MbAnnotation
wrap_MbAnnotation sem (Inh_MbAnnotation) =
    (let ( _lhsOself) = sem
     in  (Syn_MbAnnotation _lhsOself))
sem_MbAnnotation_Just :: T_Annotation ->
                         T_MbAnnotation
sem_MbAnnotation_Just just_ =
    (let _lhsOself :: MbAnnotation
         _justIself :: Annotation
         _self =
             Just _justIself
         _lhsOself =
             _self
         ( _justIself) =
             just_
     in  ( _lhsOself))
sem_MbAnnotation_Nothing :: T_MbAnnotation
sem_MbAnnotation_Nothing =
    (let _lhsOself :: MbAnnotation
         _self =
             Nothing
         _lhsOself =
             _self
     in  ( _lhsOself))
-- MbName ------------------------------------------------------
-- cata
sem_MbName :: MbName ->
              T_MbName
sem_MbName (Prelude.Just x) =
    (sem_MbName_Just (sem_Name x))
sem_MbName Prelude.Nothing =
    sem_MbName_Nothing
-- semantic domain
type T_MbName = ( MbName)
data Inh_MbName = Inh_MbName {}
data Syn_MbName = Syn_MbName {self_Syn_MbName :: MbName}
wrap_MbName :: T_MbName ->
               Inh_MbName ->
               Syn_MbName
wrap_MbName sem (Inh_MbName) =
    (let ( _lhsOself) = sem
     in  (Syn_MbName _lhsOself))
sem_MbName_Just :: T_Name ->
                   T_MbName
sem_MbName_Just just_ =
    (let _lhsOself :: MbName
         _justIself :: Name
         _self =
             Just _justIself
         _lhsOself =
             _self
         ( _justIself) =
             just_
     in  ( _lhsOself))
sem_MbName_Nothing :: T_MbName
sem_MbName_Nothing =
    (let _lhsOself :: MbName
         _self =
             Nothing
         _lhsOself =
             _self
     in  ( _lhsOself))
-- MbPattern ---------------------------------------------------
-- cata
sem_MbPattern :: MbPattern ->
                 T_MbPattern
sem_MbPattern (Prelude.Just x) =
    (sem_MbPattern_Just (sem_Pattern x))
sem_MbPattern Prelude.Nothing =
    sem_MbPattern_Nothing
-- semantic domain
type T_MbPattern = ( MbPattern)
data Inh_MbPattern = Inh_MbPattern {}
data Syn_MbPattern = Syn_MbPattern {self_Syn_MbPattern :: MbPattern}
wrap_MbPattern :: T_MbPattern ->
                  Inh_MbPattern ->
                  Syn_MbPattern
wrap_MbPattern sem (Inh_MbPattern) =
    (let ( _lhsOself) = sem
     in  (Syn_MbPattern _lhsOself))
sem_MbPattern_Just :: T_Pattern ->
                      T_MbPattern
sem_MbPattern_Just just_ =
    (let _lhsOself :: MbPattern
         _justIself :: Pattern
         _self =
             Just _justIself
         _lhsOself =
             _self
         ( _justIself) =
             just_
     in  ( _lhsOself))
sem_MbPattern_Nothing :: T_MbPattern
sem_MbPattern_Nothing =
    (let _lhsOself :: MbPattern
         _self =
             Nothing
         _lhsOself =
             _self
     in  ( _lhsOself))
-- MbSort ------------------------------------------------------
-- cata
sem_MbSort :: MbSort ->
              T_MbSort
sem_MbSort (Prelude.Just x) =
    (sem_MbSort_Just (sem_Sort x))
sem_MbSort Prelude.Nothing =
    sem_MbSort_Nothing
-- semantic domain
type T_MbSort = ( MbSort)
data Inh_MbSort = Inh_MbSort {}
data Syn_MbSort = Syn_MbSort {self_Syn_MbSort :: MbSort}
wrap_MbSort :: T_MbSort ->
               Inh_MbSort ->
               Syn_MbSort
wrap_MbSort sem (Inh_MbSort) =
    (let ( _lhsOself) = sem
     in  (Syn_MbSort _lhsOself))
sem_MbSort_Just :: T_Sort ->
                   T_MbSort
sem_MbSort_Just just_ =
    (let _lhsOself :: MbSort
         _justIself :: Sort
         _self =
             Just _justIself
         _lhsOself =
             _self
         ( _justIself) =
             just_
     in  ( _lhsOself))
sem_MbSort_Nothing :: T_MbSort
sem_MbSort_Nothing =
    (let _lhsOself :: MbSort
         _self =
             Nothing
         _lhsOself =
             _self
     in  ( _lhsOself))
-- MbTerm ------------------------------------------------------
-- cata
sem_MbTerm :: MbTerm ->
              T_MbTerm
sem_MbTerm (Prelude.Just x) =
    (sem_MbTerm_Just (sem_Term x))
sem_MbTerm Prelude.Nothing =
    sem_MbTerm_Nothing
-- semantic domain
type T_MbTerm = ( MbTerm)
data Inh_MbTerm = Inh_MbTerm {}
data Syn_MbTerm = Syn_MbTerm {self_Syn_MbTerm :: MbTerm}
wrap_MbTerm :: T_MbTerm ->
               Inh_MbTerm ->
               Syn_MbTerm
wrap_MbTerm sem (Inh_MbTerm) =
    (let ( _lhsOself) = sem
     in  (Syn_MbTerm _lhsOself))
sem_MbTerm_Just :: T_Term ->
                   T_MbTerm
sem_MbTerm_Just just_ =
    (let _lhsOself :: MbTerm
         _justIself :: Term
         _self =
             Just _justIself
         _lhsOself =
             _self
         ( _justIself) =
             just_
     in  ( _lhsOself))
sem_MbTerm_Nothing :: T_MbTerm
sem_MbTerm_Nothing =
    (let _lhsOself :: MbTerm
         _self =
             Nothing
         _lhsOself =
             _self
     in  ( _lhsOself))
-- Method ------------------------------------------------------
-- cata
sem_Method :: Method ->
              T_Method
sem_Method (Method _mthName _mthParams _mthBody) =
    (sem_Method_Method _mthName (sem_Identifiers _mthParams) (sem_Term _mthBody))
-- semantic domain
type T_Method = ( Method)
data Inh_Method = Inh_Method {}
data Syn_Method = Syn_Method {self_Syn_Method :: Method}
wrap_Method :: T_Method ->
               Inh_Method ->
               Syn_Method
wrap_Method sem (Inh_Method) =
    (let ( _lhsOself) = sem
     in  (Syn_Method _lhsOself))
sem_Method_Method :: Identifier ->
                     T_Identifiers ->
                     T_Term ->
                     T_Method
sem_Method_Method mthName_ mthParams_ mthBody_ =
    (let _lhsOself :: Method
         _mthParamsIself :: Identifiers
         _mthBodyIself :: Term
         _self =
             Method mthName_ _mthParamsIself _mthBodyIself
         _lhsOself =
             _self
         ( _mthParamsIself) =
             mthParams_
         ( _mthBodyIself) =
             mthBody_
     in  ( _lhsOself))
-- MethodDeclaration -------------------------------------------
-- cata
sem_MethodDeclaration :: MethodDeclaration ->
                         T_MethodDeclaration
sem_MethodDeclaration (MethodDeclaration _mdField _mdBinders _mdType) =
    (sem_MethodDeclaration_MethodDeclaration _mdField (sem_Binders _mdBinders) (sem_Term _mdType))
-- semantic domain
type T_MethodDeclaration = ( MethodDeclaration)
data Inh_MethodDeclaration = Inh_MethodDeclaration {}
data Syn_MethodDeclaration = Syn_MethodDeclaration {self_Syn_MethodDeclaration :: MethodDeclaration}
wrap_MethodDeclaration :: T_MethodDeclaration ->
                          Inh_MethodDeclaration ->
                          Syn_MethodDeclaration
wrap_MethodDeclaration sem (Inh_MethodDeclaration) =
    (let ( _lhsOself) = sem
     in  (Syn_MethodDeclaration _lhsOself))
sem_MethodDeclaration_MethodDeclaration :: Identifier ->
                                           T_Binders ->
                                           T_Term ->
                                           T_MethodDeclaration
sem_MethodDeclaration_MethodDeclaration mdField_ mdBinders_ mdType_ =
    (let _lhsOself :: MethodDeclaration
         _mdBindersIself :: Binders
         _mdTypeIself :: Term
         _self =
             MethodDeclaration mdField_ _mdBindersIself _mdTypeIself
         _lhsOself =
             _self
         ( _mdBindersIself) =
             mdBinders_
         ( _mdTypeIself) =
             mdType_
     in  ( _lhsOself))
-- MethodDeclarations ------------------------------------------
-- cata
sem_MethodDeclarations :: MethodDeclarations ->
                          T_MethodDeclarations
sem_MethodDeclarations list =
    (Prelude.foldr sem_MethodDeclarations_Cons sem_MethodDeclarations_Nil (Prelude.map sem_MethodDeclaration list))
-- semantic domain
type T_MethodDeclarations = ( MethodDeclarations)
data Inh_MethodDeclarations = Inh_MethodDeclarations {}
data Syn_MethodDeclarations = Syn_MethodDeclarations {self_Syn_MethodDeclarations :: MethodDeclarations}
wrap_MethodDeclarations :: T_MethodDeclarations ->
                           Inh_MethodDeclarations ->
                           Syn_MethodDeclarations
wrap_MethodDeclarations sem (Inh_MethodDeclarations) =
    (let ( _lhsOself) = sem
     in  (Syn_MethodDeclarations _lhsOself))
sem_MethodDeclarations_Cons :: T_MethodDeclaration ->
                               T_MethodDeclarations ->
                               T_MethodDeclarations
sem_MethodDeclarations_Cons hd_ tl_ =
    (let _lhsOself :: MethodDeclarations
         _hdIself :: MethodDeclaration
         _tlIself :: MethodDeclarations
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             hd_
         ( _tlIself) =
             tl_
     in  ( _lhsOself))
sem_MethodDeclarations_Nil :: T_MethodDeclarations
sem_MethodDeclarations_Nil =
    (let _lhsOself :: MethodDeclarations
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
-- Methods -----------------------------------------------------
-- cata
sem_Methods :: Methods ->
               T_Methods
sem_Methods list =
    (Prelude.foldr sem_Methods_Cons sem_Methods_Nil (Prelude.map sem_Method list))
-- semantic domain
type T_Methods = ( Methods)
data Inh_Methods = Inh_Methods {}
data Syn_Methods = Syn_Methods {self_Syn_Methods :: Methods}
wrap_Methods :: T_Methods ->
                Inh_Methods ->
                Syn_Methods
wrap_Methods sem (Inh_Methods) =
    (let ( _lhsOself) = sem
     in  (Syn_Methods _lhsOself))
sem_Methods_Cons :: T_Method ->
                    T_Methods ->
                    T_Methods
sem_Methods_Cons hd_ tl_ =
    (let _lhsOself :: Methods
         _hdIself :: Method
         _tlIself :: Methods
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             hd_
         ( _tlIself) =
             tl_
     in  ( _lhsOself))
sem_Methods_Nil :: T_Methods
sem_Methods_Nil =
    (let _lhsOself :: Methods
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
-- Modifier ----------------------------------------------------
-- cata
sem_Modifier :: Modifier ->
                T_Modifier
sem_Modifier (ModNone) =
    (sem_Modifier_ModNone)
sem_Modifier (ModLocal) =
    (sem_Modifier_ModLocal)
sem_Modifier (ModGlobal) =
    (sem_Modifier_ModGlobal)
-- semantic domain
type T_Modifier = ( Modifier)
data Inh_Modifier = Inh_Modifier {}
data Syn_Modifier = Syn_Modifier {self_Syn_Modifier :: Modifier}
wrap_Modifier :: T_Modifier ->
                 Inh_Modifier ->
                 Syn_Modifier
wrap_Modifier sem (Inh_Modifier) =
    (let ( _lhsOself) = sem
     in  (Syn_Modifier _lhsOself))
sem_Modifier_ModNone :: T_Modifier
sem_Modifier_ModNone =
    (let _lhsOself :: Modifier
         _self =
             ModNone
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_Modifier_ModLocal :: T_Modifier
sem_Modifier_ModLocal =
    (let _lhsOself :: Modifier
         _self =
             ModLocal
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_Modifier_ModGlobal :: T_Modifier
sem_Modifier_ModGlobal =
    (let _lhsOself :: Modifier
         _self =
             ModGlobal
         _lhsOself =
             _self
     in  ( _lhsOself))
-- Name --------------------------------------------------------
-- cata
sem_Name :: Name ->
            T_Name
sem_Name (NameIdent _ident) =
    (sem_Name_NameIdent _ident)
sem_Name (NameUnderscore) =
    (sem_Name_NameUnderscore)
-- semantic domain
type T_Name = ( Name)
data Inh_Name = Inh_Name {}
data Syn_Name = Syn_Name {self_Syn_Name :: Name}
wrap_Name :: T_Name ->
             Inh_Name ->
             Syn_Name
wrap_Name sem (Inh_Name) =
    (let ( _lhsOself) = sem
     in  (Syn_Name _lhsOself))
sem_Name_NameIdent :: Identifier ->
                      T_Name
sem_Name_NameIdent ident_ =
    (let _lhsOself :: Name
         _self =
             NameIdent ident_
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_Name_NameUnderscore :: T_Name
sem_Name_NameUnderscore =
    (let _lhsOself :: Name
         _self =
             NameUnderscore
         _lhsOself =
             _self
     in  ( _lhsOself))
-- Names -------------------------------------------------------
-- cata
sem_Names :: Names ->
             T_Names
sem_Names list =
    (Prelude.foldr sem_Names_Cons sem_Names_Nil (Prelude.map sem_Name list))
-- semantic domain
type T_Names = ( Names)
data Inh_Names = Inh_Names {}
data Syn_Names = Syn_Names {self_Syn_Names :: Names}
wrap_Names :: T_Names ->
              Inh_Names ->
              Syn_Names
wrap_Names sem (Inh_Names) =
    (let ( _lhsOself) = sem
     in  (Syn_Names _lhsOself))
sem_Names_Cons :: T_Name ->
                  T_Names ->
                  T_Names
sem_Names_Cons hd_ tl_ =
    (let _lhsOself :: Names
         _hdIself :: Name
         _tlIself :: Names
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             hd_
         ( _tlIself) =
             tl_
     in  ( _lhsOself))
sem_Names_Nil :: T_Names
sem_Names_Nil =
    (let _lhsOself :: Names
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
-- Pattern -----------------------------------------------------
-- cata
sem_Pattern :: Pattern ->
               T_Pattern
sem_Pattern (PatCtor _patCtor _patFields) =
    (sem_Pattern_PatCtor (sem_QualId _patCtor) (sem_Identifiers _patFields))
sem_Pattern (PatCtorEx _patCtor _patFields) =
    (sem_Pattern_PatCtorEx (sem_QualId _patCtor) (sem_Patterns _patFields))
sem_Pattern (PatUnderscore) =
    (sem_Pattern_PatUnderscore)
-- semantic domain
type T_Pattern = ( Pattern)
data Inh_Pattern = Inh_Pattern {}
data Syn_Pattern = Syn_Pattern {self_Syn_Pattern :: Pattern}
wrap_Pattern :: T_Pattern ->
                Inh_Pattern ->
                Syn_Pattern
wrap_Pattern sem (Inh_Pattern) =
    (let ( _lhsOself) = sem
     in  (Syn_Pattern _lhsOself))
sem_Pattern_PatCtor :: T_QualId ->
                       T_Identifiers ->
                       T_Pattern
sem_Pattern_PatCtor patCtor_ patFields_ =
    (let _lhsOself :: Pattern
         _patCtorIself :: QualId
         _patFieldsIself :: Identifiers
         _self =
             PatCtor _patCtorIself _patFieldsIself
         _lhsOself =
             _self
         ( _patCtorIself) =
             patCtor_
         ( _patFieldsIself) =
             patFields_
     in  ( _lhsOself))
sem_Pattern_PatCtorEx :: T_QualId ->
                         T_Patterns ->
                         T_Pattern
sem_Pattern_PatCtorEx patCtor_ patFields_ =
    (let _lhsOself :: Pattern
         _patCtorIself :: QualId
         _patFieldsIself :: Patterns
         _self =
             PatCtorEx _patCtorIself _patFieldsIself
         _lhsOself =
             _self
         ( _patCtorIself) =
             patCtor_
         ( _patFieldsIself) =
             patFields_
     in  ( _lhsOself))
sem_Pattern_PatUnderscore :: T_Pattern
sem_Pattern_PatUnderscore =
    (let _lhsOself :: Pattern
         _self =
             PatUnderscore
         _lhsOself =
             _self
     in  ( _lhsOself))
-- Patterns ----------------------------------------------------
-- cata
sem_Patterns :: Patterns ->
                T_Patterns
sem_Patterns list =
    (Prelude.foldr sem_Patterns_Cons sem_Patterns_Nil (Prelude.map sem_Pattern list))
-- semantic domain
type T_Patterns = ( Patterns)
data Inh_Patterns = Inh_Patterns {}
data Syn_Patterns = Syn_Patterns {self_Syn_Patterns :: Patterns}
wrap_Patterns :: T_Patterns ->
                 Inh_Patterns ->
                 Syn_Patterns
wrap_Patterns sem (Inh_Patterns) =
    (let ( _lhsOself) = sem
     in  (Syn_Patterns _lhsOself))
sem_Patterns_Cons :: T_Pattern ->
                     T_Patterns ->
                     T_Patterns
sem_Patterns_Cons hd_ tl_ =
    (let _lhsOself :: Patterns
         _hdIself :: Pattern
         _tlIself :: Patterns
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             hd_
         ( _tlIself) =
             tl_
     in  ( _lhsOself))
sem_Patterns_Nil :: T_Patterns
sem_Patterns_Nil =
    (let _lhsOself :: Patterns
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
-- PossiblyBracketedName ---------------------------------------
-- cata
sem_PossiblyBracketedName :: PossiblyBracketedName ->
                             T_PossiblyBracketedName
sem_PossiblyBracketedName (BracketedName _name) =
    (sem_PossiblyBracketedName_BracketedName (sem_Name _name))
sem_PossiblyBracketedName (BracedName _name) =
    (sem_PossiblyBracketedName_BracedName (sem_Name _name))
sem_PossiblyBracketedName (NormalName _name) =
    (sem_PossiblyBracketedName_NormalName (sem_Name _name))
-- semantic domain
type T_PossiblyBracketedName = ( PossiblyBracketedName)
data Inh_PossiblyBracketedName = Inh_PossiblyBracketedName {}
data Syn_PossiblyBracketedName = Syn_PossiblyBracketedName {self_Syn_PossiblyBracketedName :: PossiblyBracketedName}
wrap_PossiblyBracketedName :: T_PossiblyBracketedName ->
                              Inh_PossiblyBracketedName ->
                              Syn_PossiblyBracketedName
wrap_PossiblyBracketedName sem (Inh_PossiblyBracketedName) =
    (let ( _lhsOself) = sem
     in  (Syn_PossiblyBracketedName _lhsOself))
sem_PossiblyBracketedName_BracketedName :: T_Name ->
                                           T_PossiblyBracketedName
sem_PossiblyBracketedName_BracketedName name_ =
    (let _lhsOself :: PossiblyBracketedName
         _nameIself :: Name
         _self =
             BracketedName _nameIself
         _lhsOself =
             _self
         ( _nameIself) =
             name_
     in  ( _lhsOself))
sem_PossiblyBracketedName_BracedName :: T_Name ->
                                        T_PossiblyBracketedName
sem_PossiblyBracketedName_BracedName name_ =
    (let _lhsOself :: PossiblyBracketedName
         _nameIself :: Name
         _self =
             BracedName _nameIself
         _lhsOself =
             _self
         ( _nameIself) =
             name_
     in  ( _lhsOself))
sem_PossiblyBracketedName_NormalName :: T_Name ->
                                        T_PossiblyBracketedName
sem_PossiblyBracketedName_NormalName name_ =
    (let _lhsOself :: PossiblyBracketedName
         _nameIself :: Name
         _self =
             NormalName _nameIself
         _lhsOself =
             _self
         ( _nameIself) =
             name_
     in  ( _lhsOself))
-- PossiblyBracketedNames --------------------------------------
-- cata
sem_PossiblyBracketedNames :: PossiblyBracketedNames ->
                              T_PossiblyBracketedNames
sem_PossiblyBracketedNames list =
    (Prelude.foldr sem_PossiblyBracketedNames_Cons sem_PossiblyBracketedNames_Nil (Prelude.map sem_PossiblyBracketedName list))
-- semantic domain
type T_PossiblyBracketedNames = ( PossiblyBracketedNames)
data Inh_PossiblyBracketedNames = Inh_PossiblyBracketedNames {}
data Syn_PossiblyBracketedNames = Syn_PossiblyBracketedNames {self_Syn_PossiblyBracketedNames :: PossiblyBracketedNames}
wrap_PossiblyBracketedNames :: T_PossiblyBracketedNames ->
                               Inh_PossiblyBracketedNames ->
                               Syn_PossiblyBracketedNames
wrap_PossiblyBracketedNames sem (Inh_PossiblyBracketedNames) =
    (let ( _lhsOself) = sem
     in  (Syn_PossiblyBracketedNames _lhsOself))
sem_PossiblyBracketedNames_Cons :: T_PossiblyBracketedName ->
                                   T_PossiblyBracketedNames ->
                                   T_PossiblyBracketedNames
sem_PossiblyBracketedNames_Cons hd_ tl_ =
    (let _lhsOself :: PossiblyBracketedNames
         _hdIself :: PossiblyBracketedName
         _tlIself :: PossiblyBracketedNames
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             hd_
         ( _tlIself) =
             tl_
     in  ( _lhsOself))
sem_PossiblyBracketedNames_Nil :: T_PossiblyBracketedNames
sem_PossiblyBracketedNames_Nil =
    (let _lhsOself :: PossiblyBracketedNames
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
-- Proof -------------------------------------------------------
-- cata
sem_Proof :: Proof ->
             T_Proof
sem_Proof (ProofWith _with _proof) =
    (sem_Proof_ProofWith (sem_ProofSteps _with) (sem_ProofSteps _proof))
sem_Proof (ProofDefined _proof) =
    (sem_Proof_ProofDefined (sem_ProofSteps _proof))
sem_Proof (ProofQed _proof) =
    (sem_Proof_ProofQed (sem_ProofSteps _proof))
-- semantic domain
type T_Proof = ( Proof)
data Inh_Proof = Inh_Proof {}
data Syn_Proof = Syn_Proof {self_Syn_Proof :: Proof}
wrap_Proof :: T_Proof ->
              Inh_Proof ->
              Syn_Proof
wrap_Proof sem (Inh_Proof) =
    (let ( _lhsOself) = sem
     in  (Syn_Proof _lhsOself))
sem_Proof_ProofWith :: T_ProofSteps ->
                       T_ProofSteps ->
                       T_Proof
sem_Proof_ProofWith with_ proof_ =
    (let _lhsOself :: Proof
         _withIself :: ProofSteps
         _proofIself :: ProofSteps
         _self =
             ProofWith _withIself _proofIself
         _lhsOself =
             _self
         ( _withIself) =
             with_
         ( _proofIself) =
             proof_
     in  ( _lhsOself))
sem_Proof_ProofDefined :: T_ProofSteps ->
                          T_Proof
sem_Proof_ProofDefined proof_ =
    (let _lhsOself :: Proof
         _proofIself :: ProofSteps
         _self =
             ProofDefined _proofIself
         _lhsOself =
             _self
         ( _proofIself) =
             proof_
     in  ( _lhsOself))
sem_Proof_ProofQed :: T_ProofSteps ->
                      T_Proof
sem_Proof_ProofQed proof_ =
    (let _lhsOself :: Proof
         _proofIself :: ProofSteps
         _self =
             ProofQed _proofIself
         _lhsOself =
             _self
         ( _proofIself) =
             proof_
     in  ( _lhsOself))
-- ProofStep ---------------------------------------------------
-- cata
sem_ProofStep :: ProofStep ->
                 T_ProofStep
sem_ProofStep (PrInduction _ident) =
    (sem_ProofStep_PrInduction _ident)
sem_ProofStep (PrMutualInduction _ident _numCases) =
    (sem_ProofStep_PrMutualInduction _ident _numCases)
sem_ProofStep (PrCrushInd) =
    (sem_ProofStep_PrCrushInd)
sem_ProofStep (PrApply _term) =
    (sem_ProofStep_PrApply (sem_Term _term))
sem_ProofStep (PrApplyIn _term _ident) =
    (sem_ProofStep_PrApplyIn (sem_Term _term) _ident)
sem_ProofStep (PrExact _term) =
    (sem_ProofStep_PrExact (sem_Term _term))
sem_ProofStep (PrSeq _steps) =
    (sem_ProofStep_PrSeq (sem_ProofSteps _steps))
sem_ProofStep (PrIntros _ids) =
    (sem_ProofStep_PrIntros (sem_Identifiers _ids))
sem_ProofStep (PrRevert _ids) =
    (sem_ProofStep_PrRevert (sem_Identifiers _ids))
sem_ProofStep (PrTry _step) =
    (sem_ProofStep_PrTry (sem_ProofStep _step))
sem_ProofStep (PrConstructor) =
    (sem_ProofStep_PrConstructor)
sem_ProofStep (PrAuto) =
    (sem_ProofStep_PrAuto)
sem_ProofStep (PrFail) =
    (sem_ProofStep_PrFail)
sem_ProofStep (PrInversion _ident) =
    (sem_ProofStep_PrInversion _ident)
sem_ProofStep (PrSubst) =
    (sem_ProofStep_PrSubst)
sem_ProofStep (PrSimpl) =
    (sem_ProofStep_PrSimpl)
sem_ProofStep (PrRepeat _step) =
    (sem_ProofStep_PrRepeat (sem_ProofStep _step))
sem_ProofStep (PrRewrite _term) =
    (sem_ProofStep_PrRewrite (sem_Term _term))
sem_ProofStep (PrRewriter) =
    (sem_ProofStep_PrRewriter)
sem_ProofStep (PrEasy) =
    (sem_ProofStep_PrEasy)
sem_ProofStep (PrTactic _tactic _terms) =
    (sem_ProofStep_PrTactic _tactic (sem_Terms _terms))
sem_ProofStep (PrPoseProof _term) =
    (sem_ProofStep_PrPoseProof (sem_Term _term))
sem_ProofStep (PrPoseProofAs _term _ident) =
    (sem_ProofStep_PrPoseProofAs (sem_Term _term) _ident)
sem_ProofStep (PrBullet _lvl _subproofs) =
    (sem_ProofStep_PrBullet _lvl (sem_ProofSteps _subproofs))
sem_ProofStep (PrDestruct _term) =
    (sem_ProofStep_PrDestruct (sem_Term _term))
sem_ProofStep (PrFEqual _arity _term) =
    (sem_ProofStep_PrFEqual _arity (sem_Term _term))
sem_ProofStep (PrReflexivity) =
    (sem_ProofStep_PrReflexivity)
sem_ProofStep (PrClear _ident) =
    (sem_ProofStep_PrClear (sem_Identifiers _ident))
sem_ProofStep (PrMatchGoal _contextrules) =
    (sem_ProofStep_PrMatchGoal (sem_ContextRules _contextrules))
-- semantic domain
type T_ProofStep = ( ProofStep)
data Inh_ProofStep = Inh_ProofStep {}
data Syn_ProofStep = Syn_ProofStep {self_Syn_ProofStep :: ProofStep}
wrap_ProofStep :: T_ProofStep ->
                  Inh_ProofStep ->
                  Syn_ProofStep
wrap_ProofStep sem (Inh_ProofStep) =
    (let ( _lhsOself) = sem
     in  (Syn_ProofStep _lhsOself))
sem_ProofStep_PrInduction :: Identifier ->
                             T_ProofStep
sem_ProofStep_PrInduction ident_ =
    (let _lhsOself :: ProofStep
         _self =
             PrInduction ident_
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_ProofStep_PrMutualInduction :: Identifier ->
                                   Int ->
                                   T_ProofStep
sem_ProofStep_PrMutualInduction ident_ numCases_ =
    (let _lhsOself :: ProofStep
         _self =
             PrMutualInduction ident_ numCases_
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_ProofStep_PrCrushInd :: T_ProofStep
sem_ProofStep_PrCrushInd =
    (let _lhsOself :: ProofStep
         _self =
             PrCrushInd
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_ProofStep_PrApply :: T_Term ->
                         T_ProofStep
sem_ProofStep_PrApply term_ =
    (let _lhsOself :: ProofStep
         _termIself :: Term
         _self =
             PrApply _termIself
         _lhsOself =
             _self
         ( _termIself) =
             term_
     in  ( _lhsOself))
sem_ProofStep_PrApplyIn :: T_Term ->
                           Identifier ->
                           T_ProofStep
sem_ProofStep_PrApplyIn term_ ident_ =
    (let _lhsOself :: ProofStep
         _termIself :: Term
         _self =
             PrApplyIn _termIself ident_
         _lhsOself =
             _self
         ( _termIself) =
             term_
     in  ( _lhsOself))
sem_ProofStep_PrExact :: T_Term ->
                         T_ProofStep
sem_ProofStep_PrExact term_ =
    (let _lhsOself :: ProofStep
         _termIself :: Term
         _self =
             PrExact _termIself
         _lhsOself =
             _self
         ( _termIself) =
             term_
     in  ( _lhsOself))
sem_ProofStep_PrSeq :: T_ProofSteps ->
                       T_ProofStep
sem_ProofStep_PrSeq steps_ =
    (let _lhsOself :: ProofStep
         _stepsIself :: ProofSteps
         _self =
             PrSeq _stepsIself
         _lhsOself =
             _self
         ( _stepsIself) =
             steps_
     in  ( _lhsOself))
sem_ProofStep_PrIntros :: T_Identifiers ->
                          T_ProofStep
sem_ProofStep_PrIntros ids_ =
    (let _lhsOself :: ProofStep
         _idsIself :: Identifiers
         _self =
             PrIntros _idsIself
         _lhsOself =
             _self
         ( _idsIself) =
             ids_
     in  ( _lhsOself))
sem_ProofStep_PrRevert :: T_Identifiers ->
                          T_ProofStep
sem_ProofStep_PrRevert ids_ =
    (let _lhsOself :: ProofStep
         _idsIself :: Identifiers
         _self =
             PrRevert _idsIself
         _lhsOself =
             _self
         ( _idsIself) =
             ids_
     in  ( _lhsOself))
sem_ProofStep_PrTry :: T_ProofStep ->
                       T_ProofStep
sem_ProofStep_PrTry step_ =
    (let _lhsOself :: ProofStep
         _stepIself :: ProofStep
         _self =
             PrTry _stepIself
         _lhsOself =
             _self
         ( _stepIself) =
             step_
     in  ( _lhsOself))
sem_ProofStep_PrConstructor :: T_ProofStep
sem_ProofStep_PrConstructor =
    (let _lhsOself :: ProofStep
         _self =
             PrConstructor
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_ProofStep_PrAuto :: T_ProofStep
sem_ProofStep_PrAuto =
    (let _lhsOself :: ProofStep
         _self =
             PrAuto
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_ProofStep_PrFail :: T_ProofStep
sem_ProofStep_PrFail =
    (let _lhsOself :: ProofStep
         _self =
             PrFail
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_ProofStep_PrInversion :: Identifier ->
                             T_ProofStep
sem_ProofStep_PrInversion ident_ =
    (let _lhsOself :: ProofStep
         _self =
             PrInversion ident_
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_ProofStep_PrSubst :: T_ProofStep
sem_ProofStep_PrSubst =
    (let _lhsOself :: ProofStep
         _self =
             PrSubst
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_ProofStep_PrSimpl :: T_ProofStep
sem_ProofStep_PrSimpl =
    (let _lhsOself :: ProofStep
         _self =
             PrSimpl
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_ProofStep_PrRepeat :: T_ProofStep ->
                          T_ProofStep
sem_ProofStep_PrRepeat step_ =
    (let _lhsOself :: ProofStep
         _stepIself :: ProofStep
         _self =
             PrRepeat _stepIself
         _lhsOself =
             _self
         ( _stepIself) =
             step_
     in  ( _lhsOself))
sem_ProofStep_PrRewrite :: T_Term ->
                           T_ProofStep
sem_ProofStep_PrRewrite term_ =
    (let _lhsOself :: ProofStep
         _termIself :: Term
         _self =
             PrRewrite _termIself
         _lhsOself =
             _self
         ( _termIself) =
             term_
     in  ( _lhsOself))
sem_ProofStep_PrRewriter :: T_ProofStep
sem_ProofStep_PrRewriter =
    (let _lhsOself :: ProofStep
         _self =
             PrRewriter
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_ProofStep_PrEasy :: T_ProofStep
sem_ProofStep_PrEasy =
    (let _lhsOself :: ProofStep
         _self =
             PrEasy
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_ProofStep_PrTactic :: String ->
                          T_Terms ->
                          T_ProofStep
sem_ProofStep_PrTactic tactic_ terms_ =
    (let _lhsOself :: ProofStep
         _termsIself :: Terms
         _self =
             PrTactic tactic_ _termsIself
         _lhsOself =
             _self
         ( _termsIself) =
             terms_
     in  ( _lhsOself))
sem_ProofStep_PrPoseProof :: T_Term ->
                             T_ProofStep
sem_ProofStep_PrPoseProof term_ =
    (let _lhsOself :: ProofStep
         _termIself :: Term
         _self =
             PrPoseProof _termIself
         _lhsOself =
             _self
         ( _termIself) =
             term_
     in  ( _lhsOself))
sem_ProofStep_PrPoseProofAs :: T_Term ->
                               Identifier ->
                               T_ProofStep
sem_ProofStep_PrPoseProofAs term_ ident_ =
    (let _lhsOself :: ProofStep
         _termIself :: Term
         _self =
             PrPoseProofAs _termIself ident_
         _lhsOself =
             _self
         ( _termIself) =
             term_
     in  ( _lhsOself))
sem_ProofStep_PrBullet :: Int ->
                          T_ProofSteps ->
                          T_ProofStep
sem_ProofStep_PrBullet lvl_ subproofs_ =
    (let _lhsOself :: ProofStep
         _subproofsIself :: ProofSteps
         _self =
             PrBullet lvl_ _subproofsIself
         _lhsOself =
             _self
         ( _subproofsIself) =
             subproofs_
     in  ( _lhsOself))
sem_ProofStep_PrDestruct :: T_Term ->
                            T_ProofStep
sem_ProofStep_PrDestruct term_ =
    (let _lhsOself :: ProofStep
         _termIself :: Term
         _self =
             PrDestruct _termIself
         _lhsOself =
             _self
         ( _termIself) =
             term_
     in  ( _lhsOself))
sem_ProofStep_PrFEqual :: Int ->
                          T_Term ->
                          T_ProofStep
sem_ProofStep_PrFEqual arity_ term_ =
    (let _lhsOself :: ProofStep
         _termIself :: Term
         _self =
             PrFEqual arity_ _termIself
         _lhsOself =
             _self
         ( _termIself) =
             term_
     in  ( _lhsOself))
sem_ProofStep_PrReflexivity :: T_ProofStep
sem_ProofStep_PrReflexivity =
    (let _lhsOself :: ProofStep
         _self =
             PrReflexivity
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_ProofStep_PrClear :: T_Identifiers ->
                         T_ProofStep
sem_ProofStep_PrClear ident_ =
    (let _lhsOself :: ProofStep
         _identIself :: Identifiers
         _self =
             PrClear _identIself
         _lhsOself =
             _self
         ( _identIself) =
             ident_
     in  ( _lhsOself))
sem_ProofStep_PrMatchGoal :: T_ContextRules ->
                             T_ProofStep
sem_ProofStep_PrMatchGoal contextrules_ =
    (let _lhsOself :: ProofStep
         _contextrulesIself :: ContextRules
         _self =
             PrMatchGoal _contextrulesIself
         _lhsOself =
             _self
         ( _contextrulesIself) =
             contextrules_
     in  ( _lhsOself))
-- ProofSteps --------------------------------------------------
-- cata
sem_ProofSteps :: ProofSteps ->
                  T_ProofSteps
sem_ProofSteps list =
    (Prelude.foldr sem_ProofSteps_Cons sem_ProofSteps_Nil (Prelude.map sem_ProofStep list))
-- semantic domain
type T_ProofSteps = ( ProofSteps)
data Inh_ProofSteps = Inh_ProofSteps {}
data Syn_ProofSteps = Syn_ProofSteps {self_Syn_ProofSteps :: ProofSteps}
wrap_ProofSteps :: T_ProofSteps ->
                   Inh_ProofSteps ->
                   Syn_ProofSteps
wrap_ProofSteps sem (Inh_ProofSteps) =
    (let ( _lhsOself) = sem
     in  (Syn_ProofSteps _lhsOself))
sem_ProofSteps_Cons :: T_ProofStep ->
                       T_ProofSteps ->
                       T_ProofSteps
sem_ProofSteps_Cons hd_ tl_ =
    (let _lhsOself :: ProofSteps
         _hdIself :: ProofStep
         _tlIself :: ProofSteps
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             hd_
         ( _tlIself) =
             tl_
     in  ( _lhsOself))
sem_ProofSteps_Nil :: T_ProofSteps
sem_ProofSteps_Nil =
    (let _lhsOself :: ProofSteps
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
-- QualId ------------------------------------------------------
-- cata
sem_QualId :: QualId ->
              T_QualId
sem_QualId (Ident _ident) =
    (sem_QualId_Ident _ident)
-- semantic domain
type T_QualId = ( QualId)
data Inh_QualId = Inh_QualId {}
data Syn_QualId = Syn_QualId {self_Syn_QualId :: QualId}
wrap_QualId :: T_QualId ->
               Inh_QualId ->
               Syn_QualId
wrap_QualId sem (Inh_QualId) =
    (let ( _lhsOself) = sem
     in  (Syn_QualId _lhsOself))
sem_QualId_Ident :: Identifier ->
                    T_QualId
sem_QualId_Ident ident_ =
    (let _lhsOself :: QualId
         _self =
             Ident ident_
         _lhsOself =
             _self
     in  ( _lhsOself))
-- Root --------------------------------------------------------
-- cata
sem_Root :: Root ->
            T_Root
sem_Root (Root _sentences) =
    (sem_Root_Root (sem_Sentences _sentences))
-- semantic domain
type T_Root = ( Root)
data Inh_Root = Inh_Root {}
data Syn_Root = Syn_Root {self_Syn_Root :: Root}
wrap_Root :: T_Root ->
             Inh_Root ->
             Syn_Root
wrap_Root sem (Inh_Root) =
    (let ( _lhsOself) = sem
     in  (Syn_Root _lhsOself))
sem_Root_Root :: T_Sentences ->
                 T_Root
sem_Root_Root sentences_ =
    (let _lhsOself :: Root
         _sentencesIself :: Sentences
         _self =
             Root _sentencesIself
         _lhsOself =
             _self
         ( _sentencesIself) =
             sentences_
     in  ( _lhsOself))
-- Scheme ------------------------------------------------------
-- cata
sem_Scheme :: Scheme ->
              T_Scheme
sem_Scheme (Scheme _bodies) =
    (sem_Scheme_Scheme (sem_SchemeBodies _bodies))
-- semantic domain
type T_Scheme = ( Scheme)
data Inh_Scheme = Inh_Scheme {}
data Syn_Scheme = Syn_Scheme {self_Syn_Scheme :: Scheme}
wrap_Scheme :: T_Scheme ->
               Inh_Scheme ->
               Syn_Scheme
wrap_Scheme sem (Inh_Scheme) =
    (let ( _lhsOself) = sem
     in  (Syn_Scheme _lhsOself))
sem_Scheme_Scheme :: T_SchemeBodies ->
                     T_Scheme
sem_Scheme_Scheme bodies_ =
    (let _lhsOself :: Scheme
         _bodiesIself :: SchemeBodies
         _self =
             Scheme _bodiesIself
         _lhsOself =
             _self
         ( _bodiesIself) =
             bodies_
     in  ( _lhsOself))
-- SchemeBodies ------------------------------------------------
-- cata
sem_SchemeBodies :: SchemeBodies ->
                    T_SchemeBodies
sem_SchemeBodies list =
    (Prelude.foldr sem_SchemeBodies_Cons sem_SchemeBodies_Nil (Prelude.map sem_SchemeBody list))
-- semantic domain
type T_SchemeBodies = ( SchemeBodies)
data Inh_SchemeBodies = Inh_SchemeBodies {}
data Syn_SchemeBodies = Syn_SchemeBodies {self_Syn_SchemeBodies :: SchemeBodies}
wrap_SchemeBodies :: T_SchemeBodies ->
                     Inh_SchemeBodies ->
                     Syn_SchemeBodies
wrap_SchemeBodies sem (Inh_SchemeBodies) =
    (let ( _lhsOself) = sem
     in  (Syn_SchemeBodies _lhsOself))
sem_SchemeBodies_Cons :: T_SchemeBody ->
                         T_SchemeBodies ->
                         T_SchemeBodies
sem_SchemeBodies_Cons hd_ tl_ =
    (let _lhsOself :: SchemeBodies
         _hdIself :: SchemeBody
         _tlIself :: SchemeBodies
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             hd_
         ( _tlIself) =
             tl_
     in  ( _lhsOself))
sem_SchemeBodies_Nil :: T_SchemeBodies
sem_SchemeBodies_Nil =
    (let _lhsOself :: SchemeBodies
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
-- SchemeBody --------------------------------------------------
-- cata
sem_SchemeBody :: SchemeBody ->
                  T_SchemeBody
sem_SchemeBody (SchemeInduction _schemeIdent _schemeType) =
    (sem_SchemeBody_SchemeInduction _schemeIdent _schemeType)
-- semantic domain
type T_SchemeBody = ( SchemeBody)
data Inh_SchemeBody = Inh_SchemeBody {}
data Syn_SchemeBody = Syn_SchemeBody {self_Syn_SchemeBody :: SchemeBody}
wrap_SchemeBody :: T_SchemeBody ->
                   Inh_SchemeBody ->
                   Syn_SchemeBody
wrap_SchemeBody sem (Inh_SchemeBody) =
    (let ( _lhsOself) = sem
     in  (Syn_SchemeBody _lhsOself))
sem_SchemeBody_SchemeInduction :: Identifier ->
                                  Identifier ->
                                  T_SchemeBody
sem_SchemeBody_SchemeInduction schemeIdent_ schemeType_ =
    (let _lhsOself :: SchemeBody
         _self =
             SchemeInduction schemeIdent_ schemeType_
         _lhsOself =
             _self
     in  ( _lhsOself))
-- Sentence ----------------------------------------------------
-- cata
sem_Sentence :: Sentence ->
                T_Sentence
sem_Sentence (SentenceDefinition _definition) =
    (sem_Sentence_SentenceDefinition (sem_Definition _definition))
sem_Sentence (SentenceInductive _inductive) =
    (sem_Sentence_SentenceInductive (sem_Inductive _inductive))
sem_Sentence (SentenceFixpoint _fixpoint) =
    (sem_Sentence_SentenceFixpoint (sem_Fixpoint _fixpoint))
sem_Sentence (SentenceAssertionProof _assertion _proof) =
    (sem_Sentence_SentenceAssertionProof (sem_Assertion _assertion) (sem_Proof _proof))
sem_Sentence (SentenceSection _ident _sentences) =
    (sem_Sentence_SentenceSection _ident (sem_Sentences _sentences))
sem_Sentence (SentenceOpaque _ident) =
    (sem_Sentence_SentenceOpaque _ident)
sem_Sentence (SentenceHint _modifier _hint _databases) =
    (sem_Sentence_SentenceHint (sem_Modifier _modifier) (sem_Hint _hint) (sem_Identifiers _databases))
sem_Sentence (SentenceScheme _scheme) =
    (sem_Sentence_SentenceScheme (sem_Scheme _scheme))
sem_Sentence (SentenceCombinedScheme _combinedId _individualIds) =
    (sem_Sentence_SentenceCombinedScheme _combinedId (sem_Identifiers _individualIds))
sem_Sentence (SentenceBlankline) =
    (sem_Sentence_SentenceBlankline)
sem_Sentence (SentenceArguments _modifier _identifier _parameters) =
    (sem_Sentence_SentenceArguments (sem_Modifier _modifier) (sem_QualId _identifier) (sem_PossiblyBracketedNames _parameters))
sem_Sentence (SentenceClassDecl _classDecl) =
    (sem_Sentence_SentenceClassDecl (sem_ClassDeclaration _classDecl))
sem_Sentence (SentenceClassInst _classInst) =
    (sem_Sentence_SentenceClassInst (sem_ClassInstance _classInst))
sem_Sentence (SentenceVerbatim _verbatim) =
    (sem_Sentence_SentenceVerbatim _verbatim)
-- semantic domain
type T_Sentence = ( Sentence)
data Inh_Sentence = Inh_Sentence {}
data Syn_Sentence = Syn_Sentence {self_Syn_Sentence :: Sentence}
wrap_Sentence :: T_Sentence ->
                 Inh_Sentence ->
                 Syn_Sentence
wrap_Sentence sem (Inh_Sentence) =
    (let ( _lhsOself) = sem
     in  (Syn_Sentence _lhsOself))
sem_Sentence_SentenceDefinition :: T_Definition ->
                                   T_Sentence
sem_Sentence_SentenceDefinition definition_ =
    (let _lhsOself :: Sentence
         _definitionIself :: Definition
         _self =
             SentenceDefinition _definitionIself
         _lhsOself =
             _self
         ( _definitionIself) =
             definition_
     in  ( _lhsOself))
sem_Sentence_SentenceInductive :: T_Inductive ->
                                  T_Sentence
sem_Sentence_SentenceInductive inductive_ =
    (let _lhsOself :: Sentence
         _inductiveIself :: Inductive
         _self =
             SentenceInductive _inductiveIself
         _lhsOself =
             _self
         ( _inductiveIself) =
             inductive_
     in  ( _lhsOself))
sem_Sentence_SentenceFixpoint :: T_Fixpoint ->
                                 T_Sentence
sem_Sentence_SentenceFixpoint fixpoint_ =
    (let _lhsOself :: Sentence
         _fixpointIself :: Fixpoint
         _self =
             SentenceFixpoint _fixpointIself
         _lhsOself =
             _self
         ( _fixpointIself) =
             fixpoint_
     in  ( _lhsOself))
sem_Sentence_SentenceAssertionProof :: T_Assertion ->
                                       T_Proof ->
                                       T_Sentence
sem_Sentence_SentenceAssertionProof assertion_ proof_ =
    (let _lhsOself :: Sentence
         _assertionIself :: Assertion
         _proofIself :: Proof
         _self =
             SentenceAssertionProof _assertionIself _proofIself
         _lhsOself =
             _self
         ( _assertionIself) =
             assertion_
         ( _proofIself) =
             proof_
     in  ( _lhsOself))
sem_Sentence_SentenceSection :: Identifier ->
                                T_Sentences ->
                                T_Sentence
sem_Sentence_SentenceSection ident_ sentences_ =
    (let _lhsOself :: Sentence
         _sentencesIself :: Sentences
         _self =
             SentenceSection ident_ _sentencesIself
         _lhsOself =
             _self
         ( _sentencesIself) =
             sentences_
     in  ( _lhsOself))
sem_Sentence_SentenceOpaque :: Identifier ->
                               T_Sentence
sem_Sentence_SentenceOpaque ident_ =
    (let _lhsOself :: Sentence
         _self =
             SentenceOpaque ident_
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_Sentence_SentenceHint :: T_Modifier ->
                             T_Hint ->
                             T_Identifiers ->
                             T_Sentence
sem_Sentence_SentenceHint modifier_ hint_ databases_ =
    (let _lhsOself :: Sentence
         _modifierIself :: Modifier
         _hintIself :: Hint
         _databasesIself :: Identifiers
         _self =
             SentenceHint _modifierIself _hintIself _databasesIself
         _lhsOself =
             _self
         ( _modifierIself) =
             modifier_
         ( _hintIself) =
             hint_
         ( _databasesIself) =
             databases_
     in  ( _lhsOself))
sem_Sentence_SentenceScheme :: T_Scheme ->
                               T_Sentence
sem_Sentence_SentenceScheme scheme_ =
    (let _lhsOself :: Sentence
         _schemeIself :: Scheme
         _self =
             SentenceScheme _schemeIself
         _lhsOself =
             _self
         ( _schemeIself) =
             scheme_
     in  ( _lhsOself))
sem_Sentence_SentenceCombinedScheme :: Identifier ->
                                       T_Identifiers ->
                                       T_Sentence
sem_Sentence_SentenceCombinedScheme combinedId_ individualIds_ =
    (let _lhsOself :: Sentence
         _individualIdsIself :: Identifiers
         _self =
             SentenceCombinedScheme combinedId_ _individualIdsIself
         _lhsOself =
             _self
         ( _individualIdsIself) =
             individualIds_
     in  ( _lhsOself))
sem_Sentence_SentenceBlankline :: T_Sentence
sem_Sentence_SentenceBlankline =
    (let _lhsOself :: Sentence
         _self =
             SentenceBlankline
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_Sentence_SentenceArguments :: T_Modifier ->
                                  T_QualId ->
                                  T_PossiblyBracketedNames ->
                                  T_Sentence
sem_Sentence_SentenceArguments modifier_ identifier_ parameters_ =
    (let _lhsOself :: Sentence
         _modifierIself :: Modifier
         _identifierIself :: QualId
         _parametersIself :: PossiblyBracketedNames
         _self =
             SentenceArguments _modifierIself _identifierIself _parametersIself
         _lhsOself =
             _self
         ( _modifierIself) =
             modifier_
         ( _identifierIself) =
             identifier_
         ( _parametersIself) =
             parameters_
     in  ( _lhsOself))
sem_Sentence_SentenceClassDecl :: T_ClassDeclaration ->
                                  T_Sentence
sem_Sentence_SentenceClassDecl classDecl_ =
    (let _lhsOself :: Sentence
         _classDeclIself :: ClassDeclaration
         _self =
             SentenceClassDecl _classDeclIself
         _lhsOself =
             _self
         ( _classDeclIself) =
             classDecl_
     in  ( _lhsOself))
sem_Sentence_SentenceClassInst :: T_ClassInstance ->
                                  T_Sentence
sem_Sentence_SentenceClassInst classInst_ =
    (let _lhsOself :: Sentence
         _classInstIself :: ClassInstance
         _self =
             SentenceClassInst _classInstIself
         _lhsOself =
             _self
         ( _classInstIself) =
             classInst_
     in  ( _lhsOself))
sem_Sentence_SentenceVerbatim :: String ->
                                 T_Sentence
sem_Sentence_SentenceVerbatim verbatim_ =
    (let _lhsOself :: Sentence
         _self =
             SentenceVerbatim verbatim_
         _lhsOself =
             _self
     in  ( _lhsOself))
-- Sentences ---------------------------------------------------
-- cata
sem_Sentences :: Sentences ->
                 T_Sentences
sem_Sentences list =
    (Prelude.foldr sem_Sentences_Cons sem_Sentences_Nil (Prelude.map sem_Sentence list))
-- semantic domain
type T_Sentences = ( Sentences)
data Inh_Sentences = Inh_Sentences {}
data Syn_Sentences = Syn_Sentences {self_Syn_Sentences :: Sentences}
wrap_Sentences :: T_Sentences ->
                  Inh_Sentences ->
                  Syn_Sentences
wrap_Sentences sem (Inh_Sentences) =
    (let ( _lhsOself) = sem
     in  (Syn_Sentences _lhsOself))
sem_Sentences_Cons :: T_Sentence ->
                      T_Sentences ->
                      T_Sentences
sem_Sentences_Cons hd_ tl_ =
    (let _lhsOself :: Sentences
         _hdIself :: Sentence
         _tlIself :: Sentences
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             hd_
         ( _tlIself) =
             tl_
     in  ( _lhsOself))
sem_Sentences_Nil :: T_Sentences
sem_Sentences_Nil =
    (let _lhsOself :: Sentences
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
-- Sort --------------------------------------------------------
-- cata
sem_Sort :: Sort ->
            T_Sort
sem_Sort (Prop) =
    (sem_Sort_Prop)
sem_Sort (Set) =
    (sem_Sort_Set)
sem_Sort (Type) =
    (sem_Sort_Type)
-- semantic domain
type T_Sort = ( Sort)
data Inh_Sort = Inh_Sort {}
data Syn_Sort = Syn_Sort {self_Syn_Sort :: Sort}
wrap_Sort :: T_Sort ->
             Inh_Sort ->
             Syn_Sort
wrap_Sort sem (Inh_Sort) =
    (let ( _lhsOself) = sem
     in  (Syn_Sort _lhsOself))
sem_Sort_Prop :: T_Sort
sem_Sort_Prop =
    (let _lhsOself :: Sort
         _self =
             Prop
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_Sort_Set :: T_Sort
sem_Sort_Set =
    (let _lhsOself :: Sort
         _self =
             Set
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_Sort_Type :: T_Sort
sem_Sort_Type =
    (let _lhsOself :: Sort
         _self =
             Type
         _lhsOself =
             _self
     in  ( _lhsOself))
-- Term --------------------------------------------------------
-- cata
sem_Term :: Term ->
            T_Term
sem_Term (TermApp _appFunction _appArguments) =
    (sem_Term_TermApp (sem_Term _appFunction) (sem_Terms _appArguments))
sem_Term (TermNum _num) =
    (sem_Term_TermNum _num)
sem_Term (TermQualId _qualid) =
    (sem_Term_TermQualId (sem_QualId _qualid))
sem_Term (TermSort _sort) =
    (sem_Term_TermSort (sem_Sort _sort))
sem_Term (TermFunction _source _target) =
    (sem_Term_TermFunction (sem_Term _source) (sem_Term _target))
sem_Term (TermAbs _binders _body) =
    (sem_Term_TermAbs (sem_Binders _binders) (sem_Term _body))
sem_Term (TermForall _binders _term) =
    (sem_Term_TermForall (sem_Binders _binders) (sem_Term _term))
sem_Term (TermAnd _terms) =
    (sem_Term_TermAnd (sem_Terms _terms))
sem_Term (TermEq _left _right) =
    (sem_Term_TermEq (sem_Term _left) (sem_Term _right))
sem_Term (TermLet _id _binders _type_ _rhs _body) =
    (sem_Term_TermLet _id (sem_Binders _binders) (sem_MbTerm _type_) (sem_Term _rhs) (sem_Term _body))
sem_Term (TermUnderscore) =
    (sem_Term_TermUnderscore)
sem_Term (TermMatch _matchItem _matchReturnType _matchEquations) =
    (sem_Term_TermMatch (sem_MatchItem _matchItem) (sem_MbTerm _matchReturnType) (sem_Equations _matchEquations))
-- semantic domain
type T_Term = ( Term)
data Inh_Term = Inh_Term {}
data Syn_Term = Syn_Term {self_Syn_Term :: Term}
wrap_Term :: T_Term ->
             Inh_Term ->
             Syn_Term
wrap_Term sem (Inh_Term) =
    (let ( _lhsOself) = sem
     in  (Syn_Term _lhsOself))
sem_Term_TermApp :: T_Term ->
                    T_Terms ->
                    T_Term
sem_Term_TermApp appFunction_ appArguments_ =
    (let _lhsOself :: Term
         _appFunctionIself :: Term
         _appArgumentsIself :: Terms
         _self =
             TermApp _appFunctionIself _appArgumentsIself
         _lhsOself =
             _self
         ( _appFunctionIself) =
             appFunction_
         ( _appArgumentsIself) =
             appArguments_
     in  ( _lhsOself))
sem_Term_TermNum :: Int ->
                    T_Term
sem_Term_TermNum num_ =
    (let _lhsOself :: Term
         _self =
             TermNum num_
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_Term_TermQualId :: T_QualId ->
                       T_Term
sem_Term_TermQualId qualid_ =
    (let _lhsOself :: Term
         _qualidIself :: QualId
         _self =
             TermQualId _qualidIself
         _lhsOself =
             _self
         ( _qualidIself) =
             qualid_
     in  ( _lhsOself))
sem_Term_TermSort :: T_Sort ->
                     T_Term
sem_Term_TermSort sort_ =
    (let _lhsOself :: Term
         _sortIself :: Sort
         _self =
             TermSort _sortIself
         _lhsOself =
             _self
         ( _sortIself) =
             sort_
     in  ( _lhsOself))
sem_Term_TermFunction :: T_Term ->
                         T_Term ->
                         T_Term
sem_Term_TermFunction source_ target_ =
    (let _lhsOself :: Term
         _sourceIself :: Term
         _targetIself :: Term
         _self =
             TermFunction _sourceIself _targetIself
         _lhsOself =
             _self
         ( _sourceIself) =
             source_
         ( _targetIself) =
             target_
     in  ( _lhsOself))
sem_Term_TermAbs :: T_Binders ->
                    T_Term ->
                    T_Term
sem_Term_TermAbs binders_ body_ =
    (let _lhsOself :: Term
         _bindersIself :: Binders
         _bodyIself :: Term
         _self =
             TermAbs _bindersIself _bodyIself
         _lhsOself =
             _self
         ( _bindersIself) =
             binders_
         ( _bodyIself) =
             body_
     in  ( _lhsOself))
sem_Term_TermForall :: T_Binders ->
                       T_Term ->
                       T_Term
sem_Term_TermForall binders_ term_ =
    (let _lhsOself :: Term
         _bindersIself :: Binders
         _termIself :: Term
         _self =
             TermForall _bindersIself _termIself
         _lhsOself =
             _self
         ( _bindersIself) =
             binders_
         ( _termIself) =
             term_
     in  ( _lhsOself))
sem_Term_TermAnd :: T_Terms ->
                    T_Term
sem_Term_TermAnd terms_ =
    (let _lhsOself :: Term
         _termsIself :: Terms
         _self =
             TermAnd _termsIself
         _lhsOself =
             _self
         ( _termsIself) =
             terms_
     in  ( _lhsOself))
sem_Term_TermEq :: T_Term ->
                   T_Term ->
                   T_Term
sem_Term_TermEq left_ right_ =
    (let _lhsOself :: Term
         _leftIself :: Term
         _rightIself :: Term
         _self =
             TermEq _leftIself _rightIself
         _lhsOself =
             _self
         ( _leftIself) =
             left_
         ( _rightIself) =
             right_
     in  ( _lhsOself))
sem_Term_TermLet :: Identifier ->
                    T_Binders ->
                    T_MbTerm ->
                    T_Term ->
                    T_Term ->
                    T_Term
sem_Term_TermLet id_ binders_ type__ rhs_ body_ =
    (let _lhsOself :: Term
         _bindersIself :: Binders
         _type_Iself :: MbTerm
         _rhsIself :: Term
         _bodyIself :: Term
         _self =
             TermLet id_ _bindersIself _type_Iself _rhsIself _bodyIself
         _lhsOself =
             _self
         ( _bindersIself) =
             binders_
         ( _type_Iself) =
             type__
         ( _rhsIself) =
             rhs_
         ( _bodyIself) =
             body_
     in  ( _lhsOself))
sem_Term_TermUnderscore :: T_Term
sem_Term_TermUnderscore =
    (let _lhsOself :: Term
         _self =
             TermUnderscore
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_Term_TermMatch :: T_MatchItem ->
                      T_MbTerm ->
                      T_Equations ->
                      T_Term
sem_Term_TermMatch matchItem_ matchReturnType_ matchEquations_ =
    (let _lhsOself :: Term
         _matchItemIself :: MatchItem
         _matchReturnTypeIself :: MbTerm
         _matchEquationsIself :: Equations
         _self =
             TermMatch _matchItemIself _matchReturnTypeIself _matchEquationsIself
         _lhsOself =
             _self
         ( _matchItemIself) =
             matchItem_
         ( _matchReturnTypeIself) =
             matchReturnType_
         ( _matchEquationsIself) =
             matchEquations_
     in  ( _lhsOself))
-- Terms -------------------------------------------------------
-- cata
sem_Terms :: Terms ->
             T_Terms
sem_Terms list =
    (Prelude.foldr sem_Terms_Cons sem_Terms_Nil (Prelude.map sem_Term list))
-- semantic domain
type T_Terms = ( Terms)
data Inh_Terms = Inh_Terms {}
data Syn_Terms = Syn_Terms {self_Syn_Terms :: Terms}
wrap_Terms :: T_Terms ->
              Inh_Terms ->
              Syn_Terms
wrap_Terms sem (Inh_Terms) =
    (let ( _lhsOself) = sem
     in  (Syn_Terms _lhsOself))
sem_Terms_Cons :: T_Term ->
                  T_Terms ->
                  T_Terms
sem_Terms_Cons hd_ tl_ =
    (let _lhsOself :: Terms
         _hdIself :: Term
         _tlIself :: Terms
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             hd_
         ( _tlIself) =
             tl_
     in  ( _lhsOself))
sem_Terms_Nil :: T_Terms
sem_Terms_Nil =
    (let _lhsOself :: Terms
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
-- Variable ----------------------------------------------------
-- cata
sem_Variable :: Variable ->
                T_Variable
sem_Variable (Variable _varName _varType) =
    (sem_Variable_Variable _varName (sem_Term _varType))
-- semantic domain
type T_Variable = ( Variable)
data Inh_Variable = Inh_Variable {}
data Syn_Variable = Syn_Variable {self_Syn_Variable :: Variable}
wrap_Variable :: T_Variable ->
                 Inh_Variable ->
                 Syn_Variable
wrap_Variable sem (Inh_Variable) =
    (let ( _lhsOself) = sem
     in  (Syn_Variable _lhsOself))
sem_Variable_Variable :: Identifier ->
                         T_Term ->
                         T_Variable
sem_Variable_Variable varName_ varType_ =
    (let _lhsOself :: Variable
         _varTypeIself :: Term
         _self =
             Variable varName_ _varTypeIself
         _lhsOself =
             _self
         ( _varTypeIself) =
             varType_
     in  ( _lhsOself))