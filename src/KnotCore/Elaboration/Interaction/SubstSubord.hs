{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -Wall #-}

module KnotCore.Elaboration.Interaction.SubstSubord where

import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core

lemmas :: Elab m => [SortGroupDecl] -> m [Sentence]
lemmas sdgs = do
  ntns <- getNamespaces
  concat <$> sequenceA
    [ do
        (stna,_) <- getNamespaceCtor ntna
        depsa <- getSortNamespaceDependencies stna
        sequenceA
          [ sortDecl ntna ntnb sd
          | ntnb <- ntns
          , ntnb `notElem` depsa
          ]
    | SortGroupDecl _ sds deps _ <- sdgs,
      sd <- sds,
      ntna <- deps
    ]

sortDecl :: Elab m => NamespaceTypeName -> NamespaceTypeName -> SortDecl -> m Sentence
sortDecl ntna ntnb (SortDecl stn _ _) = localNames $ do

  (stna,_) <- getNamespaceCtor ntna

  xa      <- freshTraceVar ntna
  ta      <- freshSortVariable stna
  t       <- freshSortVariable stn

  let left   = SSubst (TS ntnb (TVar xa)) (SVar ta) (SVar t)
      right  = SSubst (TVar xa) (SVar ta) (SVar t)

  assertion <-
    TermForall
      <$> sequenceA [toBinder xa, toBinder ta]
      <*> (TermEq <$> toTerm left <*> toTerm right)

  definition <-
    Definition
    <$> idLemmaSubstSubord ntna ntnb stn
    <*> sequenceA [toBinder t]
    <*> pure (Just assertion)
    <*> (TermApp
         <$> (idLemmaSubstSubordInd ntna ntnb stn >>= toRef)
         <*> sequenceA [toRef t, toTerm HV0]
        )

  return $ SentenceDefinition definition
