
module KnotCore.Elaboration.Lemma.SubstSubstIndexCommInd where

import Control.Applicative

import qualified Coq.Syntax as Coq

import KnotCore.Syntax
import KnotCore.Elaboration.Core

lemmas :: Elab m => [NamespaceDecl] -> m [Coq.Sentence]
lemmas _ = do
  ntns <- getNamespaces
  concat <$> sequence
    [ do
        stnb  <- getSortOfNamespace ntnb
        depsb <- getSortNamespaceDependencies stnb
        sequence [ lemma ntna ntnb | ntna <- depsb ]
    | ntnb <- ntns
    ]

lemma :: Elab m => NamespaceTypeName -> NamespaceTypeName -> m Coq.Sentence
lemma ntna ntnb = localNames $ do
  stna  <- getSortOfNamespace ntna
  stnb  <- getSortOfNamespace ntnb

  xa     <- freshTraceVar ntna
  ta     <- freshSubtreeVar stna
  tb     <- freshSubtreeVar stnb
  k      <- freshHVarlistVar
  yb     <- freshIndexVar ntnb

  let left   = SSubst (TWeaken (TVar xa) (HVVar k)) (SVar ta)
                 (SSubstIndex (TWeaken (T0 ntnb) (HVVar k)) (SVar tb) (IVar yb))
      right1 = SSubst (TWeaken (T0 ntnb) (HVVar k))
                 (SSubst (TVar xa) (SVar ta) (SVar tb))
                 (SSubstIndex (TWeaken (TS ntnb (TVar xa)) (HVVar k)) (SVar ta) (IVar yb))
      right2 = SSubstIndex (TWeaken (T0 ntnb) (HVVar k)) (SSubst (TVar xa) (SVar ta) (SVar tb)) (IVar yb)
      right  = if ntna == ntnb then right1 else right2

  statement  <-
    Coq.TermForall
    <$> sequence [toBinder k, toBinder yb]
    <*> (Coq.TermEq <$> toTerm left <*> toTerm right)

  assertion <-
    Coq.Assertion
    <$> pure Coq.AssLemma
    <*> idLemmaSubstSubstIndexCommRightInd ntna ntnb
    <*> sequence [toBinder xa, toBinder ta, toBinder tb]
    <*> pure statement

  let proof :: Coq.Proof
      proof = Coq.ProofQed [Coq.PrTactic "needleGenericSubstSubstIndexCommInd" []]

  return $ Coq.SentenceAssertionProof assertion proof
