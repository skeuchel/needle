
module KnotCore.Elaboration.Lemma.LookupFunctional where

import Control.Applicative
import Control.Monad
import Data.Maybe (catMaybes)

import Coq.Syntax

import KnotCore.Syntax
import KnotCore.LookupRelation
import KnotCore.Elaboration.Core

lemmas :: Elab m => [LookupRelation] -> m [Sentence]
lemmas lks = catMaybes <$> mapM lemmaLookupFunctional lks

lemmaLookupFunctional :: Elab m => LookupRelation -> m (Maybe Sentence)
lemmaLookupFunctional (LookupRelation _ _ _ [] _ _)       = return Nothing
lemmaLookupFunctional (LookupRelation etn cn ntn stns _ _) = localNames $ do
  en        <- freshEnvVar etn
  x         <- freshIndexVar ntn
  tvs       <- mapM freshSubtreeVar stns
  tvs'      <- mapM freshSubtreeVar stns
  let ts  = map SVar tvs
      ts' = map SVar tvs'

  statement <-
    TermForall <$> sequence [toImplicitBinder en, toImplicitBinder x] <*> (
      TermForall <$> mapM toImplicitBinder tvs <*> (
        TermFunction <$> toTerm (Lookup (EVar en) (IVar x) ts) <*> (
          TermForall <$> mapM toImplicitBinder tvs' <*> (
            TermFunction
            <$> toTerm (Lookup (EVar en) (IVar x) ts')
            <*> toTerm (PAnd (zipWith PEqTerm ts ts'))
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
