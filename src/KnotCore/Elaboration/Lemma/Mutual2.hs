{-# LANGUAGE ScopedTypeVariables #-}

module KnotCore.Elaboration.Lemma.Mutual2 where

import Control.Monad
import Control.Applicative
import Data.Maybe

import Coq.StdLib
import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core
import KnotCore.Elaboration.Eq

type ProofSubtree m = SubtreeVar -> BindSpec -> Hypothesis -> m Term
type ProofCtorTerm m = m ([Binder], ProofSubtree m)
type ProofCtorVar m = CtorName -> IndexVar -> m Term

mutualInduction2 :: Elab m =>
  (SortGroupTypeName -> m Identifier) ->
  (SortTypeName -> m (Maybe Identifier)) ->
  (SubtreeVar -> m Term) ->
  (ProofCtorVar m) ->
  (ProofCtorTerm m) ->
  SortGroupDecl -> m Sentences
mutualInduction2 mkGroupLemId mkLemId mkAssertion pvar pterm sgd = localNames $ do

  let sds    = sgSorts sgd
      sgtn   = sgTypeName sgd
      stns   = map typeNameOf sds
      cdecls = [ cd | SortDecl _ _ cds <- sds, cd <- cds ]

  groupLemId  <- mkGroupLemId sgtn
  inductionId <- idInductionSortGroup sgtn

  -- Generate the statements for all sorts of this group.
  assertions <- forM sds $ \sd -> localNames $ do
                  t <- freshSubtreeVar (typeNameOf sd)
                  TermAbs
                    <$> sequence [toBinder t]
                    <*> mkAssertion t

  -- Generate proof of the entire group.
  proofs <- mapM (mkCtorProof stns mkLemId pvar pterm) cdecls

  -- DEfinition
  -- Generate the assertion of the entire group.
  definition <-
    Definition
    <$> toId groupLemId
    <*> pure []
    <*> pure Nothing
    <*> (TermApp
         <$> toRef inductionId
         <*> pure (assertions ++ proofs)
        )

  -- Generate the individual lemmas if needed
  individual <-
    case sgSorts sgd of
      [_] -> return []
      _   -> forM sds $ \sd -> do
               Just lemId <- mkLemId (typeNameOf sd)
               sv <- freshSubtreeVar (typeNameOf sd)
               lemmaRef   <- toRef groupLemId
               assertion  <- mkAssertion sv
               assertion' <- TermForall
                               <$> sequence [toBinder sv]
                               <*> pure assertion
               let proof =
                     ProofQed
                       [ PrPoseProof lemmaRef,
                         PrTactic "destruct_conjs" [],
                         PrTactic "easy" []
                       ]
               return (SentenceAssertionProof
                         (Assertion
                            AssLemma lemId [] assertion')
                         proof)

  return $ SentenceDefinition definition : individual

mkCtorProof :: Elab m =>
  [SortTypeName] -> (SortTypeName -> m (Maybe Identifier))  ->
  ProofCtorVar m -> ProofCtorTerm m -> CtorDecl -> m Term
mkCtorProof stns mkLemId pvar pterm cd =
  case cd of
    CtorVar cn mv -> localNames $ do
      x <- freshIndexVar (typeNameOf mv)
      TermAbs
        <$> sequence [toBinder x]
        <*> pvar cn x
    CtorTerm cn fds -> localNames $ do

      (binders2, proofSubtree) <- pterm
      (binders1, proofs) <-
        fmap unzip . sequence $
          [ mkFieldProof stns mkLemId proofSubtree sv bs
          | FieldSubtree sv bs <- fds
          ]

      TermAbs (concat binders1 ++ binders2)
        <$> (eqFEqualn <$> toRef cn <*> pure proofs)

mkFieldProof :: Elab m =>
  [SortTypeName] -> (SortTypeName -> m (Maybe Identifier)) ->
  ProofSubtree m -> SubtreeVar -> BindSpec -> m ([Binder], Term)
mkFieldProof stns mkLemId proofSubtree sv bs
  -- The subtree is part of this mutually recursive group.
  -- Consequently we get an induction hypothesis for it.
  | typeNameOf sv `elem` stns =
      do
        ih      <- freshInductionHypothesis sv
        binders <- sequence [toBinder sv, toBinder ih]
        proof   <- proofSubtree sv bs ih
        return (binders, proof)
  -- The subtree is from another group and the lemma is
  -- already defined so we can just call it to get the
  -- proof for this subtree.
  | otherwise =
      do
        mbLem   <- mkLemId (typeNameOf sv)
        binders <- sequence [toBinder sv]
        case mbLem of
          Just lem  -> do
            ih      <- freshInductionHypothesis sv
            proof   <- proofSubtree sv bs ih

            -- Locally bind the hypothesis for the subtree
            proof'  <-
              TermLet
              <$> toId ih
              <*> pure []
              <*> pure Nothing
              <*> (TermApp <$> toRef lem <*> sequence [toRef sv])
              <*> pure proof

            return (binders, proof')
          Nothing -> do
            proof <- toTerm (EqtRefl (typeNameOf sv))
            return (binders, proof)
