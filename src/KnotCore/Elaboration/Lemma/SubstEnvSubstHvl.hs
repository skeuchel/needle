{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module KnotCore.Elaboration.Lemma.SubstEnvSubstHvl where

import Control.Applicative
import Control.Monad

import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core

lemmass :: Elab m => [EnvDecl] -> m [Sentence]
lemmass = fmap concat . traverse lemmas

lemmas :: Elab m => EnvDecl -> m [Sentence]
lemmas (EnvDecl etn _ ecs) =
  sequenceA
  [ freshen fields >>= lemma etn (typeNameOf mv)
  | EnvCtorCons _ mv fields _mbRtn <- ecs
  ]

lemma :: Elab m => EnvTypeName -> NamespaceTypeName -> [FieldDecl 'WOMV] -> m Sentence
lemma etn ntn fds = localNames $ do

  (stn,_) <- getNamespaceCtor ntn

  en  <- freshEnvVariable etn
  t   <- freshSortVariable stn
  x   <- freshTraceVar ntn
  en1 <- freshEnvVariable etn
  en2 <- freshEnvVariable etn

  binders <-
    sequenceA
    ( toImplicitBinder en
    : toImplicitBinder t
    : eFieldDeclBinders fds
    )
  fs <- eFieldDeclFields fds

  statement <-
    TermForall
      <$> sequenceA
          [ toImplicitBinder x
          , toImplicitBinder en1
          , toImplicitBinder en2
          ]
      <*> (TermFunction
           <$> toTerm
               (SubstEnv
                 (EVar en)
                 fs
                 (SVar t)
                 (TVar x)
                 (EVar en1)
                 (EVar en2)
               )
           <*> toTerm
               (SubstHvl
                 (HVDomainEnv (EVar en))
                 (TVar x)
                 (HVDomainEnv (EVar en1))
                 (HVDomainEnv (EVar en2))
               )
          )

  lemma <- idLemmaSubstEnvSubstHvl etn ntn

  return $
    SentenceAssertionProof
      (Assertion AssLemma lemma binders statement)
      (ProofQed [PrTactic "needleGenericSubstEnvSubstHvl" []])
