
module KnotCore.Elaboration.Lemma.LookupWellformedData where

import Control.Applicative
import Control.Monad
import Data.Maybe (catMaybes)

import Coq.Syntax
import Coq.StdLib as Coq

import KnotCore.Syntax
import KnotCore.LookupRelation
import KnotCore.Elaboration.Core

lemmas :: Elab m => [LookupRelation] -> m [Sentence]
lemmas lks = catMaybes <$> mapM lemmaLookupWellformedData lks

lemmaLookupWellformedData :: Elab m => LookupRelation -> m (Maybe Sentence)
lemmaLookupWellformedData (LookupRelation _ _ _ [] _ _)        = return Nothing
lemmaLookupWellformedData (LookupRelation etn cn ntn stns _ _) = localNames $ do

  en  <- freshEnvVar etn
  x   <- freshIndexVar ntn
  tvs <- mapM freshSubtreeVar stns

  statement <-
    TermForall
    <$> sequence
        ( toImplicitBinder en
        : toImplicitBinder x
        : map toImplicitBinder tvs
        )
    <*> (TermFunction
         <$> toTerm (Lookup (EVar en) (IVar x) (map SVar tvs))
         <*> (Coq.all <$> sequence
              [ toTerm $
                WfTerm (HVDomainEnv (EVar en)) (SVar t)
              | t <- tvs
              ]
             )
        )

  lemma <- idLemmaLookupWellformedData cn

  let assertion :: Assertion
      assertion = Assertion AssLemma lemma [] statement

      proof :: Proof
      proof = ProofQed [PrTactic "needleGenericLookupWellformedData" []]

  return . Just $ SentenceAssertionProof assertion proof
