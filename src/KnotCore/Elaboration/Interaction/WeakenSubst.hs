{-# LANGUAGE GADTs #-}

module KnotCore.Elaboration.Interaction.WeakenSubst where

import qualified Coq.Syntax as Coq

import KnotCore.Syntax
import KnotCore.Elaboration.Core

lemmas :: Elab m => [SortGroupDecl] -> m [Coq.Sentence]
lemmas sgs = concat <$> traverse eSortGroupDecl sgs

eSortGroupDecl :: Elab m => SortGroupDecl -> m [Coq.Sentence]
eSortGroupDecl sg =
  sequenceA
    [ eSortDecl ntn (typeNameOf sd)
    | ntn <- sgNamespaces sg
    , sd  <- sgSorts sg
    ]

eSortDecl :: Elab m => NamespaceTypeName -> SortTypeName -> m Coq.Sentence
eSortDecl ntn stn = localNames $ do

  (stnSub,_) <- getNamespaceCtor ntn

  lemma      <- idLemmaWeakenSubst ntn stn

  h          <- freshHVarlistVar
  x          <- freshTraceVar ntn
  s          <- freshSortVariable stnSub
  t          <- freshSortVariable stn

  statement  <-
    Coq.TermForall
    <$> sequenceA [toBinder h, toBinder x, toBinder s, toBinder t]
    <*> (Coq.TermEq
         <$> toTerm (SWeaken (SSubst (TVar x) (SVar s) (SVar t)) (HVVar h))
         <*> toTerm (SSubst (TWeaken (TVar x) (HVVar h)) (SVar s) (SWeaken (SVar t) (HVVar h)))
        )

  let assertion :: Coq.Assertion
      assertion = Coq.Assertion Coq.AssLemma lemma [] statement

      proof :: Coq.Proof
      proof = Coq.ProofQed [Coq.PrTactic "needleGenericWeakenSubst" []]

  return $ Coq.SentenceAssertionProof assertion proof
