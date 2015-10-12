
module KnotCore.Elaboration.Lemma.ShiftEnvAppendEnv where

import Control.Applicative

import qualified Coq.Syntax as Coq

import KnotCore.Syntax
import KnotCore.Elaboration.Core

lemmas :: Elab m => [EnvDecl] -> m [Coq.Sentence]
lemmas eds = sequence
  [ eEnvDecl (typeNameOf mv) (typeNameOf ed)
  | ed <- eds
  , EnvCtorCons _ mv _ <- edCtors ed
  ]

eEnvDecl :: Elab m => NamespaceTypeName -> EnvTypeName -> m Coq.Sentence
eEnvDecl ntn etn = localNames $ do

  lemma      <- idLemmaShiftEnvAppendEnv ntn etn

  c          <- freshCutoffVar ntn
  d1         <- freshEnvVar etn
  d2         <- freshEnvVar etn

  statement  <-
    Coq.TermForall
    <$> sequence [toBinder c, toBinder d1, toBinder d2]
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
