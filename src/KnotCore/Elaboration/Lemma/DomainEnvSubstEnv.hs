
module KnotCore.Elaboration.Lemma.DomainEnvSubstEnv where

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

  lemma      <- idLemmaDomainEnvSubstEnv ntn etn

  (stnSub,_) <- getNamespaceCtor ntn

  x          <- freshTraceVar ntn
  s          <- freshSubtreeVar stnSub
  d          <- freshEnvVar etn

  statement  <-
    Coq.TermForall
    <$> sequence [toBinder x, toBinder s, toBinder d]
    <*> (Coq.TermEq
         <$> toTerm (HVDomainEnv (ESubst (TVar x) (SVar s) (EVar d)))
         <*> toTerm (HVDomainEnv (EVar d))
        )

  let assertion :: Coq.Assertion
      assertion = Coq.Assertion Coq.AssLemma lemma [] statement

      proof :: Coq.Proof
      proof = Coq.ProofQed [Coq.PrTactic "needleGenericDomainEnvSubstEnv" []]

  return $ Coq.SentenceAssertionProof assertion proof
