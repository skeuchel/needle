
module KnotCore.Elaboration.Lemma.LookupWellformedIndex where

import Control.Applicative
import Control.Monad
import Data.Maybe (catMaybes)

import Coq.Syntax

import KnotCore.Syntax
import KnotCore.LookupRelation
import KnotCore.Elaboration.Core
import KnotCore.Elaboration.LookupRelation

eLookupWellformedIndex :: Elab m => EnvDecl -> m [Sentence]
eLookupWellformedIndex = mkLookupRelations >=> mapM lemmaLookupWellformedIndex

lemmaLookupWellformedIndex :: Elab m => LookupRelation -> m Sentence
lemmaLookupWellformedIndex (LookupRelation etn cn ntn stns _ _) = localNames $ do

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
         <*> toTerm (WfIndex (HVDomainEnv (EVar en)) (IVar x))
        )

  lemma <- idLemmaLookupWellformedIndex cn

  let assertion :: Assertion
      assertion = Assertion AssLemma lemma [] statement

      proof :: Proof
      proof = ProofQed [PrTactic "needleGenericLookupWellformedIndex" []]

  return $ SentenceAssertionProof assertion proof
