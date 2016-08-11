{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -Wall #-}

module KnotCore.Elaboration.Interaction.SubstIndexShiftIndexReflectionInd where

import qualified Coq.Syntax as Coq

import KnotCore.Syntax
import KnotCore.Elaboration.Core


lemmas :: Elab m => [NamespaceDecl] -> m [Coq.Sentence]
lemmas = traverse (homogeneous . typeNameOf)

homogeneous :: Elab m => NamespaceTypeName -> m Coq.Sentence
homogeneous ntn = localNames $ do
  (stn,cn)   <- getNamespaceCtor ntn

  s          <- freshSortVariable stn
  h          <- freshHVarlistVar
  i          <- freshIndexVar ntn

  statement  <-
    Coq.TermForall
    <$> sequenceA [toBinder h, toBinder i]
    <*> (Coq.TermEq
         <$> toTerm (SSubstIndex (TWeaken (T0 ntn) (HVVar h)) (SVar s)
                     (IShift (CWeaken (C0 ntn) (HVVar h)) (IVar i)))
         <*> toTerm (SCtorVar stn cn (IVar i))
        )

  assertion <-
    Coq.Assertion
    <$> pure Coq.AssLemma
    <*> idLemmaSubstIndexShiftIndexReflectionInd ntn
    <*> sequenceA [toBinder s]
    <*> pure statement

  let proof :: Coq.Proof
      proof = Coq.ProofQed [Coq.PrTactic "needleGenericSubstIndexShiftIndexReflectionInd" []]

  return $ Coq.SentenceAssertionProof assertion proof
