{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -Wall #-}

module KnotCore.Elaboration.Interaction.SubstShiftComm where

import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core

lemmas :: Elab m => [SortGroupDecl] -> m [Sentence]
lemmas sdgs = concat <$>
  sequenceA
    [ traverse (sortDecl ntna ntnb) sds
    | SortGroupDecl _ sds ntns _ <- sdgs,
      ntna <- ntns,
      ntnb <- ntns
    ]

sortDecl :: Elab m => NamespaceTypeName -> NamespaceTypeName -> SortDecl -> m Sentence
sortDecl ntna ntnb (SortDecl stn _ _) = localNames $ do

  (stna,_) <- getNamespaceCtor ntna
  depsa    <- getSortNamespaceDependencies stna

  xa      <- freshTraceVar ntna
  ta      <- freshSortVariable stna
  t       <- freshSortVariable stn

  let -- α ≡ β \/ α ≢ β, β ∈ α:
      left1  = SSubst (TS ntnb (TVar xa)) (SVar ta)
                 (SShift (C0 ntnb) (SVar t))
      -- α ≢ β, β ∉ α:
      left2  = SSubst (TVar xa) (SVar ta)
                 (SShift (C0 ntnb) (SVar t))
      left  | ntna == ntnb      = left1
            | ntnb `elem` depsa = left1
            | otherwise         = left2
      right  = SShift (C0 ntnb)
                 (SSubst (TVar xa) (SVar ta) (SVar t))

  assertion <-
    TermForall
      <$> sequenceA [toBinder xa, toBinder ta]
      <*> (TermEq <$> toTerm left <*> toTerm right)

  definition <-
    Definition
    <$> idLemmaSubstShiftComm ntna ntnb stn
    <*> sequenceA [toBinder t]
    <*> pure (Just assertion)
    <*> (TermApp
         <$> (idLemmaSubstShiftCommInd ntna ntnb stn >>= toRef)
         <*> sequenceA [toRef t, toTerm HV0]
        )

  return $ SentenceDefinition definition
