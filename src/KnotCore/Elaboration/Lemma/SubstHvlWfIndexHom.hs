
module KnotCore.Elaboration.Lemma.SubstHvlWfIndexHom where

import Control.Applicative
import Control.Monad

import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core

lemmas :: Elab m => m [Sentence]
lemmas = getNamespaces >>= mapM lemma

lemma :: Elab m => NamespaceTypeName -> m Sentence
lemma ntn = localNames $ do

  (stn,_) <- getNamespaceCtor ntn

  h   <- freshHVarlistVar
  t   <- freshSubtreeVar stn
  wft <- freshVariable "wft" =<< toTerm (WfTerm (HVVar h) (SVar t))

  x   <- freshTraceVar ntn
  h1  <- freshHVarlistVar
  h2  <- freshHVarlistVar
  y   <- freshIndexVar ntn

  binders <-
    sequence
    [ toImplicitBinder h
    , toImplicitBinder t
    , toBinder wft
    ]

  statement <-
    (TermForall
     <$> sequence
         [ toImplicitBinder x
         , toImplicitBinder h1
         , toImplicitBinder h2
         ]
     <*> (TermFunction
          <$> toTerm (SubstHvl (HVVar h) (TVar x) (HVVar h1) (HVVar h2))
          <*> (TermForall
               <$> sequence [toImplicitBinder y]
               <*> (TermFunction
                    <$> toTerm (WfIndex (HVVar h1) (IVar y))
                    <*> toTerm (WfTerm (HVVar h2)
                                  (SSubstIndex (TVar x) (SVar t) (IVar y)))
                   )
              )
         )
    )

  lemma <- idLemmaSubstHvlWfIndex ntn ntn

  return $
    SentenceAssertionProof
      (Assertion AssLemma lemma binders statement)
      (ProofQed [PrTactic "needleGenericSubstHvlWfIndexHom" []])
