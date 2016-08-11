{-# LANGUAGE GADTs #-}

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
lemmas lks = catMaybes <$> traverse lemmaLookupWellformedData lks

lemmaLookupWellformedData :: Elab m => LookupRelation -> m (Maybe Sentence)
lemmaLookupWellformedData (LookupRelation _ _ _ [] _ _)        = return Nothing
lemmaLookupWellformedData (LookupRelation etn cn ntn fds _ _) = localNames $ do

  en  <- freshEnvVariable etn
  x   <- freshIndexVar ntn
  fds' <- freshen fds
  fs   <- eFieldDeclFields fds'

  statement <-
    TermForall
    <$> sequenceA
        ( toImplicitBinder en
        : toImplicitBinder x
        : eFieldDeclBinders fds'
        )
    <*> (TermFunction
         <$> toTerm (Lookup (EVar en) (IVar x) fs)
         <*> (Coq.all <$> sequenceA
              [ toTerm $
                WfSort (HVDomainEnv (EVar en)) (SVar sv)
              | FieldDeclSort _ sv _ <- fds'
              ]
             )
        )

  lemma <- idLemmaLookupWellformedData cn

  let assertion :: Assertion
      assertion = Assertion AssLemma lemma [] statement

      proof :: Proof
      proof = ProofQed [PrTactic "needleGenericLookupWellformedData" []]

  return . Just $ SentenceAssertionProof assertion proof
