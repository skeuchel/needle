
module KnotCore.Elaboration.Lemma.WeakenShift where

import Control.Applicative

import qualified Coq.Syntax as Coq

import KnotCore.Syntax
import KnotCore.Elaboration.Core

lemmas :: Elab m => [SortGroupDecl] -> m [Coq.Sentence]
lemmas sgs = concat <$> mapM eSortGroupDecl sgs

eSortGroupDecl :: Elab m => SortGroupDecl -> m [Coq.Sentence]
eSortGroupDecl sg =
  sequence
    [ eSortDecl ntn (typeNameOf sd)
    | ntn <- sgNamespaces sg
    , sd  <- sgSorts sg
    ]

eSortDecl :: Elab m => NamespaceTypeName -> SortTypeName -> m Coq.Sentence
eSortDecl ntn stn = localNames $ do

  lemma      <- idLemmaWeakenShift ntn stn

  c          <- freshCutoffVar ntn
  h          <- freshHVarlistVar
  t          <- freshSubtreeVar stn

  statement  <-
    Coq.TermForall
    <$> sequence [toBinder h, toBinder c, toBinder t]
    <*> (Coq.TermEq
         <$> toTerm (SWeaken (SShift (CVar c) (SVar t)) (HVVar h))
         <*> toTerm (SShift (CWeaken (CVar c) (HVVar h)) (SWeaken (SVar t) (HVVar h)))
        )

  let assertion :: Coq.Assertion
      assertion = Coq.Assertion Coq.AssLemma lemma [] statement

      proof :: Coq.Proof
      proof = Coq.ProofQed [Coq.PrTactic "needleGenericWeakenShift" []]

  return $ Coq.SentenceAssertionProof assertion proof
