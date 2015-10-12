
module KnotCore.Elaboration.Lemma.StabilityWeaken where

import Control.Applicative

import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core

lemmas :: Elab m => [SortGroupDecl] -> m Sentences
lemmas sdgs = concat <$>
  sequence
    [ do
        fns <- getFunctionNames (typeNameOf sd)
        mapM lemma fns
    | SortGroupDecl _ sds _ _ <- sdgs,
      sd <- sds
    ]

lemma :: Elab m => FunName -> m Sentence
lemma fn = localNames $ do

  (stn,ntn) <- getFunctionType fn

  h   <- freshHVarlistVar
  t   <- freshSubtreeVar stn

  statement <-
    TermForall
      <$> sequence
          [ toBinder h
          , toBinder t
          ]
      <*> (TermEq
           <$> toTerm (HVCall ntn fn (SWeaken (SVar t) (HVVar h)))
           <*> toTerm (HVCall ntn fn (SVar t))
          )

  lemma <- idLemmaStabilityWeaken fn

  return $
    SentenceAssertionProof
      (Assertion AssLemma lemma [] statement)
      (ProofQed [PrTactic "needleGenericStabilityWeaken" []])
