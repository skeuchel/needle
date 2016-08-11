{-# LANGUAGE GADTs #-}

module KnotCore.Elaboration.Lemma.WeakenSize where

import Control.Applicative
import Data.Maybe

import Coq.StdLib
import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core
import KnotCore.Elaboration.Eq

lemmas :: Elab m => m [Sentence]
lemmas = getSorts >>= traverse sortDecl

sortDecl :: Elab m => SortTypeName -> m Sentence
sortDecl stn = localNames $ do

  lemma <- idLemmaWeakenSize stn
  size  <- idFunctionSize stn
  t     <- freshSortVariable stn
  h     <- freshHVarlistVar

  statement <-
    TermForall
    <$> sequenceA [toBinder h, toBinder t]
    <*> (eq
         <$> (TermApp
              <$> toRef size
              <*> sequenceA [ toTerm (SWeaken (SVar t) (HVVar h)) ]
             )
         <*> (TermApp
              <$> toRef size
              <*> sequenceA [ toTerm (SVar t) ]
             )
        )

  return $
    SentenceAssertionProof
      (Assertion AssLemma lemma [] statement)
      (ProofQed [PrTactic "needleGenericWeakenSize" []])
