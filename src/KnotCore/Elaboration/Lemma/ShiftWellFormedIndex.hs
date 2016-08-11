{-# LANGUAGE GADTs #-}

module KnotCore.Elaboration.Lemma.ShiftWellFormedIndex where

import Control.Applicative

import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core

lemmas :: Elab m => m [Sentence]
lemmas = do
  ntns <- getNamespaces
  sequenceA [ lemma ntn1 ntn2 | ntn1 <- ntns, ntn2 <- ntns ]

lemma :: Elab m => NamespaceTypeName -> NamespaceTypeName -> m Sentence
lemma ntna ntnb = localNames $ do
  lemma      <- idLemmaShiftWellFormedIndex ntna ntnb

  c          <- freshCutoffVar ntna
  h1         <- freshHVarlistVar
  h2         <- freshHVarlistVar
  ins        <- freshVariable "ins" =<<
                toTerm (HVarlistInsertion (CVar c) (HVVar h1) (HVVar h2))
  i          <- freshIndexVar ntnb

  statement  <-
    TermForall
    <$> sequenceA [toBinder c, toBinder h1, toBinder h2, toBinder ins, toBinder i]
    <*> (TermFunction
         <$> toTerm (WfIndex (HVVar h1) (IVar i))
         <*> toTerm (WfIndex (HVVar h2) (IShift' (CVar c) (IVar i)))
        )

  let assertion :: Assertion
      assertion = Assertion AssLemma lemma [] statement

      proof :: Proof
      proof = ProofQed [PrTactic "needleGenericShiftWellFormedIndex" []]

  return $ SentenceAssertionProof assertion proof
