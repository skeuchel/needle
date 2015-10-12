
module KnotCore.Elaboration.Lemma.ShiftIndexCommInd where

import Control.Applicative

import qualified Coq.Syntax as Coq

import KnotCore.Syntax
import KnotCore.Elaboration.Core


lemmas :: Elab m => [NamespaceDecl] -> m [Coq.Sentence]
lemmas = mapM (homogeneous . typeNameOf)

homogeneous :: Elab m => NamespaceTypeName -> m Coq.Sentence
homogeneous ntn = localNames $ do
  lemma      <- idLemmaShiftIndexCommInd ntn

  c          <- freshCutoffVar ntn
  h          <- freshHVarlistVar
  i          <- freshIndexVar ntn

  statement  <-
    Coq.TermForall
    <$> sequence [toBinder h, toBinder c, toBinder i]
    <*> (Coq.TermEq
         <$> toTerm (IShift (CWeaken (CS (CVar c)) (HVVar h))
                     (IShift (CWeaken (C0 ntn) (HVVar h)) (IVar i)))
         <*> toTerm (IShift (CWeaken (C0 ntn) (HVVar h))
                     (IShift (CWeaken (CVar c) (HVVar h)) (IVar i)))
        )

  let assertion :: Coq.Assertion
      assertion = Coq.Assertion Coq.AssLemma lemma [] statement

      proof :: Coq.Proof
      proof = Coq.ProofQed [Coq.PrTactic "needleGenericShiftIndexCommInd" []]

  return $ Coq.SentenceAssertionProof assertion proof
