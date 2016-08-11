{-# LANGUAGE GADTs #-}

module KnotCore.Elaboration.Lemma.DomainEnvShiftEnv where

import Control.Applicative

import qualified Coq.Syntax as Coq

import KnotCore.Syntax
import KnotCore.Elaboration.Core

lemmas :: Elab m => [EnvDecl] -> m [Coq.Sentence]
lemmas eds = sequenceA
  [ eEnvDecl (typeNameOf bv) (typeNameOf ed)
  | ed <- eds
  , EnvCtorCons _cn bv _fds _mbRtn <- edCtors ed
  ]

eEnvDecl :: Elab m => NamespaceTypeName -> EnvTypeName -> m Coq.Sentence
eEnvDecl ntn etn = localNames $ do

  lemma      <- idLemmaDomainEnvShiftEnv ntn etn

  c          <- freshCutoffVar ntn
  d          <- freshEnvVariable etn

  statement  <-
    Coq.TermForall
    <$> sequenceA [toBinder c, toBinder d]
    <*> (Coq.TermEq
         <$> toTerm (HVDomainEnv (EShift (CVar c) (EVar d)))
         <*> toTerm (HVDomainEnv (EVar d))
        )

  let assertion :: Coq.Assertion
      assertion = Coq.Assertion Coq.AssLemma lemma [] statement

      proof :: Coq.Proof
      proof = Coq.ProofQed [Coq.PrTactic "needleGenericDomainEnvShiftEnv" []]

  return $ Coq.SentenceAssertionProof assertion proof
