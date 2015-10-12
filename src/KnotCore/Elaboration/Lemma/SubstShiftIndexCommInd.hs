
module KnotCore.Elaboration.Lemma.SubstShiftIndexCommInd where

import Control.Applicative

import qualified Coq.Syntax as Coq

import KnotCore.Syntax
import KnotCore.Elaboration.Core

lemmas :: Elab m => [NamespaceDecl] -> m [Coq.Sentence]
lemmas nds =
  sequence
    [ lemma ntna ntnb
    | ntna <- map typeNameOf nds,
      ntnb <- map typeNameOf nds
    ]

lemma :: Elab m => NamespaceTypeName -> NamespaceTypeName -> m Coq.Sentence
lemma ntna ntnb = localNames $ do
  (stna,_)   <- getNamespaceCtor ntna
  depsa <- getSortNamespaceDependencies stna

  xa           <- freshTraceVar ntna
  ta           <- freshSubtreeVar stna
  h            <- freshHVarlistVar
  ya           <- freshIndexVar ntna

  let -- α ≡ β:
      lefthom  = SSubstIndex (TWeaken (TS ntnb (TVar xa)) (HVVar h)) (SVar ta)
                   (IShift (CWeaken (C0 ntnb) (HVVar h)) (IVar ya))
      -- α ≢ β, β ∈ α:
      lefthet  = SSubstIndex (TWeaken (TS ntnb (TVar xa)) (HVVar h)) (SVar ta)
                   (IVar ya)
      left     = if ntna == ntnb then lefthom else lefthet
      right1   = SShift (CWeaken (C0 ntnb) (HVVar h))
                   (SSubstIndex (TWeaken (TVar xa) (HVVar h)) (SVar ta) (IVar ya))
      right2   = SSubstIndex (TWeaken (TVar xa) (HVVar h)) (SVar ta) (IVar ya)
      right    = if ntnb `elem` depsa then right1 else right2
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
