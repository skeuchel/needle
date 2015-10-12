
module KnotCore.Elaboration.Lemma.SubstIndexSubordInd where

import Control.Applicative

import qualified Coq.Syntax as Coq

import KnotCore.Syntax
import KnotCore.Elaboration.Core

lemmas :: Elab m => [NamespaceDecl] -> m [Coq.Sentence]
lemmas nds = concat <$>
  sequence
    [ do
        (stna,_)   <- getNamespaceCtor ntna
        deps <- getSortNamespaceDependencies stna
        sequence
          [ lemma ntna ntnb
          | ntnb <- map typeNameOf nds
          , ntnb `notElem` deps
          ]
    | ntna <- map typeNameOf nds
    ]

lemma :: Elab m => NamespaceTypeName -> NamespaceTypeName -> m Coq.Sentence
lemma ntna ntnb = localNames $ do
  (stna,_)   <- getNamespaceCtor ntna

  xa           <- freshTraceVar ntna
  ta           <- freshSubtreeVar stna
  h            <- freshHVarlistVar
  ya           <- freshIndexVar ntna

  let lefthom  = SSubstIndex (TWeaken (TS ntnb (TVar xa)) (HVVar h)) (SVar ta) (IVar ya)
      lefthet  = SSubstIndex (TWeaken (TS ntnb (TVar xa)) (HVVar h)) (SVar ta)
                   (IVar ya)
      left     = if ntna == ntnb then lefthom else lefthet
      right    = SShift (CWeaken (C0 ntnb) (HVVar h))
                   (SSubstIndex (TWeaken (TVar xa) (HVVar h)) (SVar ta) (IVar ya))

  statement  <-
    Coq.TermForall
    <$> sequence [toBinder h, toBinder ya]
    <*> (Coq.TermEq <$> toTerm left <*> toTerm right)

  assertion <-
    Coq.Assertion
    <$> pure Coq.AssLemma
    <*> idLemmaSubstShiftIndexCommInd ntna ntnb
    <*> sequence [toBinder xa, toBinder ta]
    <*> pure statement

  let proof :: Coq.Proof
      proof = Coq.ProofQed [Coq.PrTactic "needleGenericShiftSubstIndexCommInd" []]

  return $ Coq.SentenceAssertionProof assertion proof
