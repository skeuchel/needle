{-# LANGUAGE GADTs #-}

module KnotCore.Elaboration.Lemma.ShiftEnvAppendEnv where

import qualified Coq.Syntax as Coq

import KnotCore.Syntax
import KnotCore.Elaboration.Core

import Control.Applicative

lemmas :: Elab m => [EnvDecl] -> m [Coq.Sentence]
lemmas eds = sequenceA
  [ eEnvDecl (typeNameOf bv) (typeNameOf ed)
  | ed <- eds
  , EnvCtorCons _cn bv _fds _mbRtn <- edCtors ed
  ]

eEnvDecl :: Elab m => NamespaceTypeName -> EnvTypeName -> m Coq.Sentence
eEnvDecl ntn etn = localNames $ do

  lemma      <- idLemmaShiftEnvAppendEnv ntn etn

  c          <- freshCutoffVar ntn
  d1         <- freshEnvVariable etn
  d2         <- freshEnvVariable etn

  statement  <-
    Coq.TermForall
    <$> sequenceA [toBinder c, toBinder d1, toBinder d2]
    <*> (Coq.TermEq
         <$> toTerm (EShift (CVar c) (EAppend (EVar d1) (EVar d2)))
         <*> toTerm (EAppend
                      (EShift (CVar c) (EVar d1))
                      (EShift (CWeaken (CVar c) (HVDomainEnv (EVar d1))) (EVar d2)))
        )

  let assertion :: Coq.Assertion
      assertion = Coq.Assertion Coq.AssLemma lemma [] statement

      proof :: Coq.Proof
      proof = Coq.ProofQed [Coq.PrTactic "needleGenericShiftEnvAppendEnv" []]

  return $ Coq.SentenceAssertionProof assertion proof
