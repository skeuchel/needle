
module KnotCore.Elaboration.Lemma.DomainEnvShiftEnv where

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

  lemma      <- idLemmaDomainEnvShiftEnv ntn etn

  c          <- freshCutoffVar ntn
  d          <- freshEnvVar etn

  statement  <-
    Coq.TermForall
    <$> sequence [toBinder c, toBinder d]
    <*> (Coq.TermEq
         <$> toTerm (HVDomainEnv (EShift (CVar c) (EVar d)))
         <*> toTerm (HVDomainEnv (EVar d))
        )

  let assertion :: Coq.Assertion
      assertion = Coq.Assertion Coq.AssLemma lemma [] statement

      proof :: Coq.Proof
      proof = Coq.ProofQed [Coq.PrTactic "needleGenericDomainEnvShiftEnv" []]

  return $ Coq.SentenceAssertionProof assertion proof
