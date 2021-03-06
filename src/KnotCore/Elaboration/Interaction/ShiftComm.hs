{-# LANGUAGE GADTs #-}

module KnotCore.Elaboration.Interaction.ShiftComm where

import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core

lemmas :: Elab m => [SortGroupDecl] -> m [Sentence]
lemmas sdgs = concat <$>
  sequenceA
    [ traverse (sortDecl ntn1 ntn2) sds
    | SortGroupDecl _ sds ntns _ <- sdgs,
      ntn1 <- ntns, ntn2 <- ntns
    ]

sortDecl :: Elab m =>
            NamespaceTypeName ->
            NamespaceTypeName ->
            SortDecl ->
            m Sentence
sortDecl ntn1 ntn2 (SortDecl stn _ _) = localNames $ do

  t       <- freshSortVariable stn
  c       <- freshCutoffVar ntn1

  let lefthom = SShift (CS (CVar c)) (SShift (C0 ntn2) (SVar t))
      lefthet = SShift (CVar c) (SShift (C0 ntn2) (SVar t))
      left    = if ntn1 == ntn2 then lefthom else lefthet
      right   = SShift (C0 ntn2) (SShift (CVar c) (SVar t))

  assertion <-
    TermForall
      <$> sequenceA [toBinder c]
      <*> (TermEq <$> toTerm left <*> toTerm right)

  definition <-
    Definition
    <$> idLemmaShiftComm ntn1 ntn2 stn
    <*> sequenceA [toBinder t]
    <*> pure (Just assertion)
    <*> (TermApp
         <$> (idLemmaShiftCommInd ntn1 ntn2 stn >>= toRef)
         <*> sequenceA [toRef t, toTerm HV0]
        )

  return $ SentenceDefinition definition
