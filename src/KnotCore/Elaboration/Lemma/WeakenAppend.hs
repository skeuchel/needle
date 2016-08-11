{-# LANGUAGE GADTs #-}

module KnotCore.Elaboration.Lemma.WeakenAppend where

import Control.Applicative

import qualified Coq.Syntax as Coq

import KnotCore.Syntax
import KnotCore.Elaboration.Core

lemmas :: Elab m => [SortGroupDecl] -> m [Coq.Sentence]
lemmas sgs = concat <$> traverse eSortGroupDecl sgs

eSortGroupDecl :: Elab m => SortGroupDecl -> m [Coq.Sentence]
eSortGroupDecl sg =
  sequenceA
    [ eSortDecl (typeNameOf sd)
    | sd  <- sgSorts sg
    ]

eSortDecl :: Elab m => SortTypeName -> m Coq.Sentence
eSortDecl stn = localNames $ do

  lemma      <- idLemmaWeakenAppend stn

  t          <- freshSortVariable stn
  h1         <- freshHVarlistVar
  h2         <- freshHVarlistVar

  statement  <-
    Coq.TermForall
    <$> sequenceA [toBinder t, toBinder h1, toBinder h2]
    <*> (Coq.TermEq
         <$> toTerm (SWeaken (SWeaken (SVar t) (HVVar h1)) (HVVar h2))
         <*> toTerm (SWeaken (SVar t) (HVAppend (HVVar h1) (HVVar h2)))
        )

  let assertion :: Coq.Assertion
      assertion = Coq.Assertion Coq.AssLemma lemma [] statement

      proof :: Coq.Proof
      proof = Coq.ProofQed [Coq.PrTactic "needleGenericWeakenAppend" []]

  return $ Coq.SentenceAssertionProof assertion proof
