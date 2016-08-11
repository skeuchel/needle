{-# LANGUAGE GADTs #-}

module KnotCore.Elaboration.Lemma.DomainEnvAppendEnv where

import Control.Applicative

import qualified Coq.Syntax as Coq

import KnotCore.Syntax
import KnotCore.Elaboration.Core

lemmas :: Elab m => [EnvDecl] -> m [Coq.Sentence]
lemmas = traverse (eEnvDecl . typeNameOf)

eEnvDecl :: Elab m => EnvTypeName -> m Coq.Sentence
eEnvDecl etn = localNames $ do

  lemma      <- idLemmaDomainEnvAppendEnv etn

  d1         <- freshEnvVariable etn
  d2         <- freshEnvVariable etn

  statement  <-
    Coq.TermForall
    <$> sequenceA [toBinder d1, toBinder d2]
    <*> (Coq.TermEq
         <$> toTerm (HVDomainEnv (EAppend (EVar d1) (EVar d2)))
         <*> toTerm (HVAppend (HVDomainEnv (EVar d1)) (HVDomainEnv (EVar d2)))
        )

  let assertion :: Coq.Assertion
      assertion = Coq.Assertion Coq.AssLemma lemma [] statement

      proof :: Coq.Proof
      proof = Coq.ProofQed [Coq.PrTactic "needleGenericDomainEnvAppendEnv" []]

  return $ Coq.SentenceAssertionProof assertion proof
