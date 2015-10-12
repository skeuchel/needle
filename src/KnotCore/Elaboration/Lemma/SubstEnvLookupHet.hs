
module KnotCore.Elaboration.Lemma.SubstEnvLookupHet where

import Control.Applicative
import Control.Monad
import Data.Set (Set)
import qualified Data.Set as S

import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core

lemmass :: Elab m => [EnvDecl] -> m [Sentence]
lemmass = fmap concat . mapM lemmas

lemmas :: Elab m => EnvDecl -> m [Sentence]
lemmas (EnvDecl etn _ ecs) =
  sequence
  [ lemma etn subNtn subFields lkNtn lkFields
  | EnvCtorCons _ subMv subFields <- ecs
  , EnvCtorCons _ lkMv lkFields <- ecs
  , let subNtn = typeNameOf subMv
        lkNtn  = typeNameOf lkMv
  , subNtn /= lkNtn
  ]

lemma :: Elab m =>
  EnvTypeName ->
  NamespaceTypeName -> [SubtreeVar] ->
  NamespaceTypeName -> [SubtreeVar] ->
  m Sentence
lemma etn subNtn subFields lkNtn lkFields = localNames $ do

  subStn    <- getSortOfNamespace subNtn
  en        <- freshEnvVar etn
  en1       <- freshEnvVar etn
  en2       <- freshEnvVar etn
  subTs     <- mapM freshen subFields
  s         <- freshSubtreeVar subStn
  wfs       <- freshVariable "wf" =<<
               toTerm (WfTerm (HVDomainEnv (EVar en)) (SVar s))
  x         <- freshTraceVar subNtn
  y         <- freshIndexVar lkNtn
  lkTs      <- mapM freshen lkFields
  lkDeps    <- S.fromList . concat <$>
               mapM (getSortNamespaceDependencies . typeNameOf) lkFields
  binders   <- sequence $ concat
               [ [toImplicitBinder en]
               , map toImplicitBinder subTs
               , [toImplicitBinder s]
               , [toBinder wfs | S.member subNtn lkDeps]
               ]
  substEnv  <- freshVariable "sub" =<<
               toTerm (SubstEnv (EVar en) (map SVar subTs) (SVar s) (TVar x)
                        (EVar en1) (EVar en2))

  statement <-
    TermForall
    <$> sequence
        ( toImplicitBinder x
        : toImplicitBinder en1
        : toImplicitBinder en2
        : toBinder substEnv
        : toImplicitBinder y
        : map toImplicitBinder lkTs
        )
    <*> (TermFunction
         <$> toTerm (Lookup (EVar en1) (IVar y) (map SVar lkTs))
         <*> toTerm
             (Lookup (EVar en2)
              (IVar y)
              [SSubst' (TVar x) (SVar s) (SVar t) | t <- lkTs]
             )
        )

  lemma <- idLemmaSubstEnvLookup etn subNtn lkNtn

  return $
    SentenceAssertionProof
      (Assertion AssLemma lemma binders statement)
      (ProofQed [PrTactic "needleGenericSubstEnvLookup" []])
