
module KnotCore.Elaboration.Lemma.InsertEnvInsertHvl where

import Control.Applicative
import Control.Monad

import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core

lemmass :: Elab m => [EnvDecl] -> m [Sentence]
lemmass = fmap concat . mapM lemmas

lemmas :: Elab m => EnvDecl -> m [Sentence]
lemmas (EnvDecl etn _ ecs) =
  sequence
  [ lemma etn (typeNameOf mv)
  | EnvCtorCons _ mv _ <- ecs
  ]

lemma :: Elab m => EnvTypeName -> NamespaceTypeName -> m Sentence
lemma etn ntn = localNames $ do

  c   <- freshCutoffVar ntn
  en1 <- freshEnvVar etn
  en2 <- freshEnvVar etn

  statement <-
    TermForall
      <$> sequence
          [ toImplicitBinder c
          , toImplicitBinder en1
          , toImplicitBinder en2
          ]
      <*> (TermFunction
           <$> toTerm
               (InsertEnv
                 (CVar c)
                 (EVar en1)
                 (EVar en2)
               )
           <*> toTerm
               (HVarlistInsertion
                 (CVar c)
                 (HVDomainEnv (EVar en1))
                 (HVDomainEnv (EVar en2))
               )
          )

  lemma <- idLemmaInsertEnvInsertHvl etn ntn

  return $
    SentenceAssertionProof
      (Assertion AssLemma lemma [] statement)
      (ProofQed [PrTactic "needleGenericInsertEnvInsertHvl" []])
