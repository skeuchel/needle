

module KnotCore.Elaboration.Lemma.LookupInversionHere where

import Control.Applicative
import Control.Monad
import Data.Maybe (catMaybes)

import Coq.Syntax

import KnotCore.Syntax
import KnotCore.LookupRelation
import KnotCore.Elaboration.Core

lemmas :: Elab m => [LookupRelation] -> m [Sentence]
lemmas lks = catMaybes <$> mapM lemmaLookupInversionHere lks

lemmaLookupInversionHere :: Elab m =>
                            LookupRelation ->
                            m (Maybe Sentence)
lemmaLookupInversionHere (LookupRelation _ _ _ [] _ _)        = return Nothing
lemmaLookupInversionHere (LookupRelation etn cn ntn stns _ _) = localNames $ do
  en   <- freshEnvVar etn
  (stn,_) <- getNamespaceCtor ntn
  tvs1 <- mapM freshSubtreeVar stns
  tvs2 <- mapM freshSubtreeVar stns
  let ts1 = map SVar tvs1
      ts2 = map SVar tvs2

  statement <- TermForall
               <$> sequence (toBinder en :
                             map toBinder tvs1 ++
                             map toBinder tvs2)
               <*> (foldr1 TermFunction <$> sequence
                      [ toTerm (Lookup (ECtor cn (EVar en) ts1) (I0 ntn stn) ts2)
                      , toTerm (PAnd (zipWith PEqTerm (map (SShift' (C0 ntn)) ts1) ts2))
                      ]
                   )

  lemma <- idLookupInversionHere cn

  let assertion :: Assertion
      assertion = Assertion AssLemma lemma [] statement

      proof :: Proof
      proof = ProofQed [PrTactic "needleGenericLookupInversion" []]

  return . Just $ SentenceAssertionProof assertion proof
