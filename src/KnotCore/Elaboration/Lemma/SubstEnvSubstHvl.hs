
module KnotCore.Elaboration.Lemma.SubstEnvSubstHvl where

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
  [ freshen fields >>= lemma etn (typeNameOf mv)
  | EnvCtorCons _ mv fields <- ecs
  ]

lemma :: Elab m => EnvTypeName -> NamespaceTypeName -> [SubtreeVar] -> m Sentence
lemma etn ntn ts = localNames $ do

  (stn,_) <- getNamespaceCtor ntn

  en  <- freshEnvVar etn
  t   <- freshSubtreeVar stn
  x   <- freshTraceVar ntn
  en1 <- freshEnvVar etn
  en2 <- freshEnvVar etn

  binders <-
    sequence
    ( toImplicitBinder en
    : toImplicitBinder t
    : map toImplicitBinder ts
    )

  statement <-
    TermForall
      <$> sequence
          [ toImplicitBinder x
          , toImplicitBinder en1
          , toImplicitBinder en2
          ]
      <*> (TermFunction
           <$> toTerm
               (SubstEnv
                 (EVar en)
                 (map SVar ts)
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
