{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -Wall #-}

module KnotCore.Elaboration.Interaction.SubstShiftReflection where

import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core

lemmas :: Elab m => [SortGroupDecl] -> m [Sentence]
lemmas sdgs = concat <$>
  sequenceA
    [ traverse (sortDecl ntn) sds
    | SortGroupDecl _ sds ntns _ <- sdgs,
      ntn <- ntns
    ]

sortDecl :: Elab m => NamespaceTypeName -> SortDecl -> m Sentence
sortDecl ntn (SortDecl congStn _ _) = localNames $ do

  (subStn,_) <- getNamespaceCtor ntn
  s          <- freshSortVariable subStn
  t          <- freshSortVariable congStn

  let left    = SSubst (T0 ntn) (SVar s) (SShift (C0 ntn) (SVar t))
      right   = SVar t

  assertion <-
    TermForall
      <$> sequenceA [toBinder s]
      <*> (TermEq <$> toTerm left <*> toTerm right)

  definition <-
    Definition
    <$> idLemmaSubstShiftReflection ntn congStn
    <*> sequenceA [toBinder t]
    <*> pure (Just assertion)
    <*> (TermApp
         <$> (idLemmaSubstShiftReflectionInd ntn congStn >>= toRef)
         <*> sequenceA [toRef t, toTerm HV0]
        )

  return $ SentenceDefinition definition
