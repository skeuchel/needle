
module KnotCore.Elaboration.Lemma.SubstSubstIndexCommLeftInd where

import Control.Applicative

import qualified Coq.Syntax as Coq

import KnotCore.Syntax
import KnotCore.Elaboration.Core

lemmas :: Elab m => [NamespaceDecl] -> m [Coq.Sentence]
lemmas _ = do
  ntns <- getNamespaces
  concat <$> sequence
    [ do
        stna  <- getSortOfNamespace ntna
        depsa <- getSortNamespaceDependencies stna
        sequence [ lemma ntna ntnb
                 | ntnb <- depsa, ntna /= ntnb
                 ]
    | ntna <- ntns
    ]

lemma :: Elab m => NamespaceTypeName -> NamespaceTypeName -> m Coq.Sentence
lemma ntna ntnb = localNames $ do

  stna  <- getSortOfNamespace ntna
  stnb  <- getSortOfNamespace ntnb
  depsb <- getSortNamespaceDependencies stnb

  xa     <- freshTraceVar ntna
  ta     <- freshSubtreeVar stna
  tb     <- freshSubtreeVar stnb
  k      <- freshHVarlistVar
  ya     <- freshIndexVar ntna

  let left   = SSubstIndex (TWeaken (TVar xa) (HVVar k)) (SVar ta) (IVar ya)
      right  = SSubst (TWeaken (T0 ntnb) (HVVar k))
                 (SSubst' (TVar xa) (SVar ta) (SVar tb))
                 (SSubstIndex
                    (TWeaken (TS ntnb (TVar xa)) (HVVar k))
                    (SVar ta) (IVar ya))

  statement  <-
    Coq.TermForall
    <$> sequence [toBinder k, toBinder ya]
    <*> (Coq.TermEq <$> toTerm left <*> toTerm right)

  assertion <-
    Coq.Assertion
    <$> pure Coq.AssLemma
    <*> idLemmaSubstSubstIndexCommLeftInd ntna ntnb
    <*> sequence [toBinder xa, toBinder ta, toBinder tb]
    <*> pure statement

  let proof :: Coq.Proof
      proof = Coq.ProofQed [Coq.PrTactic "needleGenericSubstSubstIndexCommInd" []]

  return $ Coq.SentenceAssertionProof assertion proof
