{-# LANGUAGE GADTs #-}

module KnotCore.Elaboration.Interaction.SubstSubstComm where

import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core

lemmas :: Elab m => [SortGroupDecl] -> m [Sentence]
lemmas sdgs = concat <$>
  sequenceA
    [ traverse (sortDecl ntna ntnb) sds
    | SortGroupDecl _ sds ntns _ <- sdgs
    , ntna <- ntns
    , ntnb <- ntns
    ]

sortDecl :: Elab m => NamespaceTypeName -> NamespaceTypeName -> SortDecl -> m Sentence
sortDecl ntna ntnb (SortDecl stn _ _) = localNames $ do

  stna   <- getSortOfNamespace ntna
  stnb   <- getSortOfNamespace ntnb
  depsa  <- getSortNamespaceDependencies stna
  depsb  <- getSortNamespaceDependencies stnb

  xa     <- freshTraceVar ntna
  ta     <- freshSortVariable stna
  tb     <- freshSortVariable stnb
  t      <- freshSortVariable stn

  let left    = SSubst (TVar xa) (SVar ta)                              (SSubst (T0 ntnb) (SVar tb) (SVar t))
      -- 1. α ∈ β, β ∈ α
      right1  = SSubst (T0 ntnb) (SSubst (TVar xa) (SVar ta) (SVar tb)) (SSubst (TS ntnb (TVar xa)) (SVar ta) (SVar t))
      -- 2. α ∈ β, β ∉ α
      right2  = SSubst (T0 ntnb) (SSubst (TVar xa) (SVar ta) (SVar tb)) (SSubst (TVar xa) (SVar ta) (SVar t))
      -- 3. α ∉ β, β ∈ α
      right3  = SSubst (T0 ntnb) (SVar tb)                              (SSubst (TS ntnb (TVar xa)) (SVar ta) (SVar t))
      -- 4. α ∉ β, β ∉ α
      right4  = SSubst (T0 ntnb) (SVar tb)                              (SSubst (TVar xa) (SVar ta) (SVar t))

      ainb    = ntna `elem` depsb
      bina    = ntnb `elem` depsa

      right |     ainb &&     bina = right1
            |     ainb && not bina = right2
            | not ainb &&     bina = right3
            | not ainb && not bina = right4
            | otherwise            = error "IMPOSSIBLE"

  assertion <-
    TermForall
      <$> sequenceA [toBinder xa, toBinder ta, toBinder tb]
      <*> (TermEq <$> toTerm left <*> toTerm right)

  definition <-
    Definition
    <$> idLemmaSubstSubstComm ntna ntnb stn
    <*> sequenceA [toBinder t]
    <*> pure (Just assertion)
    <*> (TermApp
         <$> (idLemmaSubstSubstCommInd ntna ntnb stn >>= toRef)
         <*> sequenceA [toRef t, toTerm HV0]
        )

  return $ SentenceDefinition definition
