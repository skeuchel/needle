
module KnotCore.Elaboration.Lemma.SubstIndexShiftIndexReflectionInd where

import Control.Applicative

import qualified Coq.Syntax as Coq

import KnotCore.Syntax
import KnotCore.Elaboration.Core


lemmas :: Elab m => [NamespaceDecl] -> m [Coq.Sentence]
lemmas = mapM (homogeneous . typeNameOf)

homogeneous :: Elab m => NamespaceTypeName -> m Coq.Sentence
homogeneous ntn = localNames $ do
  (stn,cn)   <- getNamespaceCtor ntn

  s          <- freshSubtreeVar stn
  h          <- freshHVarlistVar
  i          <- freshIndexVar ntn

  statement  <-
    Coq.TermForall
    <$> sequence [toBinder h, toBinder i]
    <*> (Coq.TermEq
         <$> toTerm (SSubstIndex (TWeaken (T0 ntn) (HVVar h)) (SVar s)
                     (IShift (CWeaken (C0 ntn) (HVVar h)) (IVar i)))
         <*> toTerm (SCtorVar cn (IVar i))
        )

  assertion <-
    Coq.Assertion
    <$> pure Coq.AssLemma
    <*> idLemmaSubstIndexShiftIndexReflectionInd ntn
    <*> sequence [toBinder s]
    <*> pure statement

  let proof :: Coq.Proof
      proof = Coq.ProofQed [Coq.PrTactic "needleGenericSubstIndexShiftIndexReflectionInd" []]

  return $ Coq.SentenceAssertionProof assertion proof
