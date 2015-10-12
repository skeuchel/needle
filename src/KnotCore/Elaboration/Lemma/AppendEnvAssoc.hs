
module KnotCore.Elaboration.Lemma.AppendEnvAssoc where

import Control.Applicative

import qualified Coq.Syntax as Coq

import KnotCore.Syntax
import KnotCore.Elaboration.Core

lemmas :: Elab m => [EnvDecl] -> m [Coq.Sentence]
lemmas eds = mapM (eEnvDecl . typeNameOf)  eds

eEnvDecl :: Elab m => EnvTypeName -> m Coq.Sentence
eEnvDecl etn = localNames $ do

  lemma      <- idLemmaAppendEnvAssoc etn

  g          <- freshEnvVar etn
  d1         <- freshEnvVar etn
  d2         <- freshEnvVar etn

  statement  <-
    Coq.TermForall
    <$> sequence [toBinder g, toBinder d1, toBinder d2]
    <*> (Coq.TermEq
         <$> toTerm (EAppend (EVar g) (EAppend (EVar d1) (EVar d2)))
         <*> toTerm (EAppend (EAppend (EVar g) (EVar d1)) (EVar d2))
        )

  let assertion :: Coq.Assertion
      assertion = Coq.Assertion Coq.AssLemma lemma [] statement

      proof :: Coq.Proof
      proof = Coq.ProofQed [Coq.PrTactic "needleGenericAppendEnvAssoc" []]

  return $ Coq.SentenceAssertionProof assertion proof
