{-# LANGUAGE GADTs #-}

module KnotCore.Elaboration.Lemma.StabilityWeaken where

import Control.Applicative

import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core

lemmas :: Elab m => [SortGroupDecl] -> m Sentences
lemmas sdgs = concat <$>
  sequenceA
    [ do
        fns <- getFunctionNames (typeNameOf sd)
        traverse lemma fns
    | SortGroupDecl _ sds _ _ <- sdgs,
      sd <- sds
    ]

lemma :: Elab m => FunName -> m Sentence
lemma fn = localNames $ do

  (stn,_ntn) <- getFunctionType fn

  h   <- freshHVarlistVar
  t   <- freshSortVariable stn

  statement <-
    TermForall
      <$> sequenceA
          [ toBinder h
          , toBinder t
          ]
      <*> (TermEq
           <$> toTerm (HVCall fn (SWeaken (SVar t) (HVVar h)))
           <*> toTerm (HVCall fn (SVar t))
          )

  lemma <- idLemmaStabilityWeaken fn

  return $
    SentenceAssertionProof
      (Assertion AssLemma lemma [] statement)
      (ProofQed [PrTactic "needleGenericStabilityWeaken" []])
