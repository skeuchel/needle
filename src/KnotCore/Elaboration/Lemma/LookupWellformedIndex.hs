{-# LANGUAGE GADTs #-}

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
eLookupWellformedIndex = mkLookupRelations >=> traverse lemmaLookupWellformedIndex

lemmaLookupWellformedIndex :: Elab m => LookupRelation -> m Sentence
lemmaLookupWellformedIndex (LookupRelation etn cn ntn fds _ _) = localNames $ do

  en  <- freshEnvVariable etn
  x   <- freshIndexVar ntn
  fds' <- freshen fds
  fs  <- eFieldDeclFields fds'

  statement <-
    TermForall
    <$> sequenceA
        ( toImplicitBinder en
        : toImplicitBinder x
        : eFieldDeclBinders fds'
        )
    <*> (TermFunction
         <$> toTerm (Lookup (EVar en) (IVar x) fs)
         <*> toTerm (WfIndex (HVDomainEnv (EVar en)) (IVar x))
        )

  lemma <- idLemmaLookupWellformedIndex cn

  let assertion :: Assertion
      assertion = Assertion AssLemma lemma [] statement

      proof :: Proof
      proof = ProofQed [PrTactic "needleGenericLookupWellformedIndex" []]

  return $ SentenceAssertionProof assertion proof
