
module KnotCore.Elaboration.Lemma.ShiftSubstIndexCommInd where

import Control.Applicative

import qualified Coq.Syntax as Coq

import KnotCore.Syntax
import KnotCore.Elaboration.Core

lemmas :: Elab m => [NamespaceDecl] -> m [Coq.Sentence]
lemmas nds = concat <$>
  sequence
    [ do
        (stnb,_)   <- getNamespaceCtor ntnb
        deps <- getSortNamespaceDependencies stnb
        sequence [ lemma ntna ntnb | ntna <- deps ]
    | ntnb <- map typeNameOf nds
    ]

lemma :: Elab m => NamespaceTypeName -> NamespaceTypeName -> m Coq.Sentence
lemma ntna ntnb = localNames $ do
  (stnb,_)   <- getNamespaceCtor ntnb

  ca           <- freshCutoffVar ntna
  sb           <- freshSubtreeVar stnb
  h            <- freshHVarlistVar
  yb           <- freshIndexVar ntnb

  let left     = SShift (CWeaken (CVar ca) (HVVar h))
                   (SSubstIndex (TWeaken (T0 ntnb) (HVVar h)) (SVar sb) (IVar yb))
      righthom = SSubstIndex (TWeaken (T0 ntnb) (HVVar h)) (SShift (CVar ca) (SVar sb))
                   (IShift (CWeaken (CS (CVar ca)) (HVVar h)) (IVar yb))
      righthet = SSubstIndex (TWeaken (T0 ntnb) (HVVar h)) (SShift (CVar ca) (SVar sb)) (IVar yb)
      right    = if ntna == ntnb then righthom else righthet

  statement  <-
    Coq.TermForall
    <$> sequence [toBinder h, toBinder yb]
    <*> (Coq.TermEq <$> toTerm left <*> toTerm right)

  assertion <-
    Coq.Assertion
    <$> pure Coq.AssLemma
    <*> idLemmaShiftSubstIndexCommInd ntna ntnb
    <*> sequence [toBinder ca, toBinder sb]
    <*> pure statement

  let proof :: Coq.Proof
      proof = Coq.ProofQed [Coq.PrTactic "needleGenericShiftSubstIndexCommInd" []]

  return $ Coq.SentenceAssertionProof assertion proof
