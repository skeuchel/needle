{-# LANGUAGE GADTs #-}

module KnotCore.Elaboration.Lemma.LookupFunctional where

import Control.Applicative
import Control.Monad
import Data.Maybe (catMaybes)

import Coq.Syntax

import KnotCore.Syntax
import KnotCore.LookupRelation
import KnotCore.Elaboration.Core

lemmas :: Elab m => [LookupRelation] -> m [Sentence]
lemmas lks = catMaybes <$> traverse lemmaLookupFunctional lks

lemmaLookupFunctional :: Elab m => LookupRelation -> m (Maybe Sentence)
lemmaLookupFunctional (LookupRelation _ _ _ [] _ _)       = return Nothing
lemmaLookupFunctional (LookupRelation etn cn ntn fds _ _) = localNames $ do
  en   <- freshEnvVariable etn
  x    <- freshIndexVar ntn
  fds1 <- freshen fds
  fds2 <- freshen fds
  fs1  <- eFieldDeclFields fds1
  fs2  <- eFieldDeclFields fds2

  statement <-
    TermForall <$> sequenceA [toImplicitBinder en, toImplicitBinder x] <*> (
      TermForall <$> sequenceA (eFieldDeclBinders fds1) <*> (
        TermFunction <$> toTerm (Lookup (EVar en) (IVar x) fs1) <*> (
          TermForall <$> sequenceA (eFieldDeclBinders fds2) <*> (
            TermFunction
            <$> toTerm (Lookup (EVar en) (IVar x) fs2)
            <*> toTerm (PAnd (zipWith PEqField fs1 fs2))
          )
        )
      )
    )

  lemma <- idLemmaLookupFunctional cn

  let assertion :: Assertion
      assertion = Assertion AssLemma lemma [] statement

      proof :: Proof
      proof = ProofQed [PrTactic "needleGenericLookupFunctional" []]

  return . Just $ SentenceAssertionProof assertion proof
