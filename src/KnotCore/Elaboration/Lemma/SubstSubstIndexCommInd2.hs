
module KnotCore.Elaboration.Lemma.SubstSubstIndexCommInd where

import Control.Applicative

import qualified Coq.Syntax as Coq

import KnotCore.Syntax
import KnotCore.Elaboration.Core

lemmas :: Elab m => [NamespaceDecl] -> m [Coq.Sentence]
lemmas _ = do
  ntns <- getNamespaces
  sequence
    [ do
        lemma ntna
    | ntna <- map typeNameOf nds
    ]

lemma :: Elab m => NamespaceTypeName -> NamespaceTypeName m Coq.Sentence
lemma ntna = localNames $ do
  (stna,_)   <- getNamespaceCtor ntna

  xa           <- freshTraceVar ntna
  ta1          <- freshSubtreeVar stna
  ta2          <- freshSubtreeVar stna
  h            <- freshHVarlistVar
  ya           <- freshIndexVar ntna

  let left   = SSubst (TWeaken (TVar xa) (HVVar h)) (SVar ta2)
                 (SSubstIndex (TWeaken (T0 ntna) (HVVar h)) (SVar ta1) (IVar ya))
      right  = SSubst (TWeaken (T0 ntna) (HVVar h))
                 (SSubst (TVar xa) (SVar ta2) (SVar ta1))
                 (SSubstIndex (TWeaken (TS ntna (TVar xa)) (HVVar h)) (SVar ta2) (IVar ya))

  statement  <-
    Coq.TermForall
    <$> sequence [toBinder h, toBinder ya]
    <*> (Coq.TermEq <$> toTerm left <*> toTerm right)

  assertion <-
    Coq.Assertion
    <$> pure Coq.AssLemma
    <*> idLemmaSubstSubstIndexCommInd ntna ntna
    <*> sequence [toBinder xa, toBinder ta1, toBinder ta2]
    <*> pure statement

  let proof :: Coq.Proof
      proof = Coq.ProofQed [Coq.PrTactic "needleGenericSubstSubstIndexCommInd" []]

  return $ Coq.SentenceAssertionProof assertion proof
