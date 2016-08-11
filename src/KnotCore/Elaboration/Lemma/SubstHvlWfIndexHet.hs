{-# LANGUAGE GADTs #-}

module KnotCore.Elaboration.Lemma.SubstHvlWfIndexHet where

import Control.Applicative
import Control.Monad

import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core

lemmas :: Elab m => m [Sentence]
lemmas = do
  ntns <- getNamespaces
  sequenceA [ lemma ntna ntnb | ntna <- ntns, ntnb <- ntns, ntna /= ntnb ]

lemma :: Elab m => NamespaceTypeName -> NamespaceTypeName -> m Sentence
lemma ntna ntnb = localNames $ do

  h   <- freshHVarlistVar
  x   <- freshTraceVar ntna
  h1  <- freshHVarlistVar
  h2  <- freshHVarlistVar
  y   <- freshIndexVar ntnb

  binders <- sequenceA [ toImplicitBinder h ]

  statement <-
    TermForall
    <$> sequenceA
        [ toImplicitBinder x
        , toImplicitBinder h1
        , toImplicitBinder h2
        ]
    <*> (TermFunction
         <$> toTerm (SubstHvl (HVVar h) (TVar x) (HVVar h1) (HVVar h2))
         <*> (TermForall
              <$> sequenceA [toImplicitBinder y]
              <*> (TermFunction
                   <$> toTerm (WfIndex (HVVar h1) (IVar y))
                   <*> toTerm (WfIndex (HVVar h2) (IVar y))
                  )
             )
        )


  lemma <- idLemmaSubstHvlWfIndex ntna ntnb

  return $
    SentenceAssertionProof
      (Assertion AssLemma lemma binders statement)
      (ProofQed [PrTactic "needleGenericSubstHvlWfIndexHet" []])
