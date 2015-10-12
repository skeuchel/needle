{-# LANGUAGE ScopedTypeVariables #-}

module KnotCore.Elaboration.Lemma.Mutual where

import Control.Applicative
import Control.Monad
import Data.Maybe

import qualified Coq.StdLib as Coq
import qualified Coq.Syntax as Coq

import KnotCore.Syntax
import KnotCore.Elaboration.Core

type ProofCtor m = CtorDecl -> m (Coq.ProofSteps, ProofSubtree m)
type ProofSubtree m = SubtreeVar -> BindSpec -> Hypothesis -> m Coq.ProofSteps

mutualInduction :: Elab m =>
  (SortGroupTypeName -> m Coq.Identifier) ->
  (SortTypeName -> m (Maybe Coq.Identifier)) ->
  (SortDecl -> m Coq.Term) ->
  ProofCtor m ->
  SortGroupDecl -> m Coq.Sentences
mutualInduction groupLemmaIdentifier lemmaIdentifier mkAssertion proofCtor
  (SortGroupDecl sgtn sds _ _) =
  do
    groupLemmaIdent <- groupLemmaIdentifier sgtn
    inductionIdent  <- idInductionSortGroup sgtn
    assertions      <- mapM (localNames . mkAssertion) sds

    -- Generate the assertion of the entire group.
    let assertion = Coq.Assertion
                      Coq.AssLemma groupLemmaIdent []
                      (Coq.all assertions)

    -- Generate proof of the entire group.
    prfs <- mapM (freshen >=> mkCtorProof) cdecls
    let proof =
          Coq.ProofQed $
            Coq.PrMutualInduction inductionIdent (length cdecls) :
            map (Coq.PrBullet 0) prfs

    -- Generate the individual lemmas if needed
    individual <-
      case sds of
        [_] -> return []
        _   -> mapM (\sd ->
                       do
                         Just lemmaId <- lemmaIdentifier (typeNameOf sd)
                         lemmaRef <- toRef groupLemmaIdent
                         assertion  <- mkAssertion sd
                         let proof =
                               Coq.ProofQed
                                 [ Coq.PrPoseProof lemmaRef,
                                   Coq.PrTactic "destruct_conjs" [],
                                   Coq.PrTactic "easy" []
                                 ]
                         return (Coq.SentenceAssertionProof
                                   (Coq.Assertion
                                      Coq.AssLemma lemmaId [] assertion)
                                   proof)
                    ) sds

    return $
      [ Coq.SentenceAssertionProof assertion proof,
        Coq.SentenceBlankline
      ] ++ individual


  where
    stns   = map typeNameOf sds
    cdecls = [ cd | SortDecl _ _ cds <- sds, cd <- cds ]

    --mkFieldProof :: SubtreeVar ->
    --  BindSpec -> m ([Coq.Identifier], Coq.ProofSteps, Maybe Coq.ProofSteps)
    mkFieldProof proofSubtree sn bs
      -- The subtree is part of this mutually recursive group.
      -- Consequently we get an induction hypothesis for it.
      | typeNameOf sn `elem` stns =
          do
            ih   <- freshInductionHypothesis sn
            snId <- toId sn
            ihId <- hypothesisIdentifier ih
            prf  <- proofSubtree sn bs ih
            return ([snId,ihId], [], Just prf)
      -- The subtree is from another group and the lemma is
      -- already defined so we can just call it to get the
      -- proof for this subtree.
      | otherwise =
          do
            mbLem <- lemmaIdentifier (typeNameOf sn)
            snId  <- toId sn
            snRef <- toRef sn
            case mbLem of
              Just lem ->
                do
                  lemRef <- toRef lem
                  ih     <- freshInductionHypothesis sn
                  ihId   <- hypothesisIdentifier ih
                  prf    <- proofSubtree sn bs ih
                  return ([snId],
                          [ Coq.PrPoseProofAs
                             (Coq.TermApp lemRef [snRef])
                             ihId
                          ], Just prf)
              Nothing -> return ([snId], [], Just [Coq.PrReflexivity])

    --mkCtorProof :: CtorDecl -> m Coq.ProofSteps
    mkCtorProof cd@(CtorVar{}) = fst <$> proofCtor cd
    mkCtorProof cd@(CtorTerm _ fds) =
      do
        (prfInit, proofSubtree) <- proofCtor cd
        (intros, pose , prfs) <-
          fmap unzip3 . sequence $
            [ mkFieldProof proofSubtree sn bs
            | FieldSubtree sn bs <- fds
            ]
        return $
          (let xs = concat  intros
           in if null xs then [] else [Coq.PrIntros xs]) ++
          concat pose ++
          prfInit ++
          map (Coq.PrBullet 1) (catMaybes prfs)
