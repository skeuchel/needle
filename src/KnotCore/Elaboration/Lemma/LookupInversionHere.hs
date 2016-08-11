{-# LANGUAGE GADTs #-}

module KnotCore.Elaboration.Lemma.LookupInversionHere where

import Control.Applicative
import Control.Monad
import Data.Maybe (catMaybes)

import Coq.Syntax

import KnotCore.Syntax
import KnotCore.LookupRelation
import KnotCore.Elaboration.Core

lemmas :: Elab m => [LookupRelation] -> m [Sentence]
lemmas lks = catMaybes <$> traverse lemmaLookupInversionHere lks

lemmaLookupInversionHere :: Elab m =>
                            LookupRelation ->
                            m (Maybe Sentence)
lemmaLookupInversionHere (LookupRelation _ _ _ [] _ _)        = return Nothing
lemmaLookupInversionHere (LookupRelation etn cn ntn fds _ _) = localNames $ do
  en   <- freshEnvVariable etn
  (stn,_) <- getNamespaceCtor ntn
  fds1 <- freshen fds
  fds2 <- freshen fds
  fs1  <- eFieldDeclFields fds1
  fs2  <- eFieldDeclFields fds2

  statement <- TermForall
               <$> sequenceA (toBinder en :
                             eFieldDeclBinders fds1 ++
                             eFieldDeclBinders fds2)
               <*> (foldr1 TermFunction <$> sequenceA
                      [ toTerm (Lookup (ECons (EVar en) ntn fs1) (I0 ntn stn) fs2)
                      , toTerm (PAnd (zipWith PEqField (map (shiftField (C0 ntn)) fs1) fs2))
                      ]
                   )

  lemma <- idLookupInversionHere cn

  let assertion :: Assertion
      assertion = Assertion AssLemma lemma [] statement

      proof :: Proof
      proof = ProofQed [PrTactic "needleGenericLookupInversion" []]

  return . Just $ SentenceAssertionProof assertion proof
