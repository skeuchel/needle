{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module KnotCore.Elaboration.Lemma.SubstEnvLookupHet where

import Control.Applicative
import Control.Monad
import Data.Set (Set)
import qualified Data.Set as S

import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core

lemmass :: Elab m => [EnvDecl] -> m [Sentence]
lemmass = fmap concat . traverse lemmas

lemmas :: Elab m => EnvDecl -> m [Sentence]
lemmas (EnvDecl etn _ ecs) =
  sequenceA
  [ lemma etn subNtn subFields lkNtn lkFields
  | EnvCtorCons _ subMv subFields _mbRtn <- ecs
  , EnvCtorCons _ lkMv lkFields _mbRtn <- ecs
  , let subNtn = typeNameOf subMv
        lkNtn  = typeNameOf lkMv
  , subNtn /= lkNtn
  ]

lemma :: Elab m =>
  EnvTypeName ->
  NamespaceTypeName -> [FieldDecl 'WOMV] ->
  NamespaceTypeName -> [FieldDecl 'WOMV] ->
  m Sentence
lemma etn subNtn subFields lkNtn lkFields = localNames $ do

  subStn    <- getSortOfNamespace subNtn
  en        <- freshEnvVariable etn
  en1       <- freshEnvVariable etn
  en2       <- freshEnvVariable etn
  subFds    <- freshen subFields
  subFs     <- eFieldDeclFields subFds
  s         <- freshSortVariable subStn
  wfs       <- freshVariable "wf" =<<
               toTerm (WfSort (HVDomainEnv (EVar en)) (SVar s))
  x         <- freshTraceVar subNtn
  y         <- freshIndexVar lkNtn
  lkFds     <- freshen lkFields
  lkFs      <- eFieldDeclFields lkFds
  lkDeps    <- S.fromList . concat <$>
               traverse getSortNamespaceDependencies
                 [ typeNameOf sv | FieldDeclSort _ sv _ <- lkFields ]
  binders   <- sequenceA $ concat
               [ [toImplicitBinder en]
               , eFieldDeclBinders subFds
               , [toImplicitBinder s]
               , [toBinder wfs | S.member subNtn lkDeps]
               ]
  substEnv  <- freshVariable "sub" =<<
               toTerm (SubstEnv (EVar en) subFs (SVar s) (TVar x)
                        (EVar en1) (EVar en2))

  statement <-
    TermForall
    <$> sequenceA
        ( toImplicitBinder x
        : toImplicitBinder en1
        : toImplicitBinder en2
        : toBinder substEnv
        : toImplicitBinder y
        : eFieldDeclBinders lkFds
        )
    <*> (TermFunction
         <$> toTerm (Lookup (EVar en1) (IVar y) lkFs)
         <*> toTerm
             (Lookup (EVar en2)
              (IVar y)
              (map (substField (TVar x) (SVar s)) lkFs)
             )
        )

  lemma <- idLemmaSubstEnvLookup etn subNtn lkNtn

  return $
    SentenceAssertionProof
      (Assertion AssLemma lemma binders statement)
      (ProofQed [PrTactic "needleGenericSubstEnvLookup" []])
