{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}

module KnotCore.Elaboration.Interaction.SubstShiftCommInd (lemmas) where

import Coq.StdLib as Coq
import Coq.Syntax as Coq

import KnotCore.Syntax
import KnotCore.Elaboration.Core
import KnotCore.Elaboration.Eq
import KnotCore.Elaboration.Interaction.Common

lemmas :: Elab m => [SortGroupDecl] -> m [Coq.Sentence]
lemmas sdgs =
  sequenceA
    [ localNames $ do
        (stna,_) <- getNamespaceCtor ntna

        k       <- freshHVarlistVar
        xa      <- freshTraceVar ntna
        ta      <- freshSortVariable stna
        sortDeclGroup ntna ntnb k xa ta sdg
    | sdg@(SortGroupDecl _ _ ntns _) <- sdgs,
      ntna <- ntns,
      ntnb <- ntns
    ]

sortDeclGroup :: forall m. Elab m => NamespaceTypeName -> NamespaceTypeName ->
  HVarlistVar -> TraceVar -> SortVariable -> SortGroupDecl -> m Sentence
sortDeclGroup ntna ntnb k xa ta sgd = do
  binders <- sequenceA [toBinder k, toBinder xa, toBinder ta]
  termInduction
    (idLemmaSubstShiftCommInd ntna ntnb) binders
    goal proofVar proofField (sgSorts sgd)
  where

    goal :: SortVariable -> m Term
    goal sv = do
      depsa    <- getSortNamespaceDependencies (typeNameOf ta)

      let -- α ≡ β \/ α ≢ β, β ∈ α:
          left1  = SSubst (TWeaken (TS ntnb (TVar xa)) (HVVar k)) (SVar ta)
                     (SShift (CWeaken (C0 ntnb) (HVVar k)) (SVar sv))
          -- α ≢ β, β ∉ α:
          left2  = SSubst (TWeaken (TVar xa) (HVVar k)) (SVar ta)
                     (SShift (CWeaken (C0 ntnb) (HVVar k)) (SVar sv))
          left  | ntnb == ntna      = left1
                | ntnb `elem` depsa = left1
                | otherwise         = left2
          right  = SShift (CWeaken (C0 ntnb) (HVVar k))
                     (SSubst (TWeaken (TVar xa) (HVVar k)) (SVar ta) (SVar sv))

      Coq.eq <$> toTerm left <*> toTerm right

    proofVar :: CtorName -> IndexVar -> m Term
    proofVar _ x = do

      depsa    <- getSortNamespaceDependencies (typeNameOf ta)

      if ntna == typeNameOf x && ntnb `elem` depsa
        then
          Coq.TermApp
            <$> (idLemmaSubstShiftIndexCommInd ntna ntnb >>= toRef)
            <*> sequenceA [toRef xa, toRef ta, toRef k, toRef x]
        else
          pure Coq.eqRefl

    proofField :: BindSpec -> SortVariable -> m Term
    proofField bs sv = do
      let stn = typeNameOf sv
          ebs = evalBindSpec HV0 bs
          stna = typeNameOf ta
      ih <- Coq.TermApp
            <$> (idLemmaSubstShiftCommInd ntna ntnb stn >>= toRef)
            <*> sequenceA
                [ toRef sv
                , toTerm (HVAppend (HVVar k) ebs)
                , toRef xa
                , toRef ta
                ]

      bsSubsta <- EqhCongAppend (EqhRefl HV0) <$> eqhvlEvalBindspecSubst ntna bs
      bsShiftb <- EqhCongAppend (EqhRefl HV0) <$> eqhvlEvalBindspecShift ntnb bs
      let -- shift_subst0_hom_comm
          -- subst_shift0_het_comm1
          proof0 = foldr1 EqtTrans
                   [ EqtCongSubst
                       (EqxTrans
                          (EqxCongWeaken (EqxRefl ntna) bsShiftb)
                          (EqxWeakenAppend (TS ntnb (TVar xa)) (HVVar k) ebs))
                       (EqtRefl stna)
                       (EqtCongShift
                          (EqcWeakenAppend (C0 ntnb) (HVVar k) ebs)
                          (EqtRefl stn))
                   , EqtAssumption stn ih
                   , EqtSym $
                       EqtCongShift
                         (EqcTrans
                            (EqcCongWeaken (EqcRefl ntnb) bsSubsta)
                            (EqcWeakenAppend (C0 ntnb) (HVVar k) ebs))
                         (EqtCongSubst
                            (EqxWeakenAppend (TVar xa) (HVVar k) ebs)
                            (EqtRefl stna)
                            (EqtRefl stn))
                   ]
          proof2 = EqtCongShift
                     (EqcCongWeaken (EqcRefl ntnb) (EqhSym bsSubsta))
                     (EqtRefl stn)
          -- shift_subst0_het_comm2
          proof3 = foldr1 EqtTrans
                   [ EqtCongSubst
                       (EqxTrans
                          (EqxCongWeaken (EqxRefl ntna) bsShiftb)
                          (EqxWeakenAppend (TVar xa) (HVVar k) ebs))
                       (EqtRefl stna)
                          (EqtCongShift
                             (EqcWeakenAppend (C0 ntnb) (HVVar k) ebs)
                             (EqtRefl stn))
                   , EqtAssumption stn ih
                   , EqtSym $
                       EqtCongShift
                         (EqcTrans
                            (EqcCongWeaken (EqcRefl ntnb) bsSubsta)
                            (EqcWeakenAppend (C0 ntnb) (HVVar k) ebs))
                         (EqtCongSubst
                            (EqxWeakenAppend (TVar xa) (HVVar k) ebs)
                            (EqtRefl stna)
                            (EqtRefl stn))

                   ]
          proof4 = EqtCongSubst
                     (EqxCongWeaken (EqxRefl ntna) bsShiftb)
                     (EqtRefl stna) (EqtRefl stn)
          proof5 = EqtCongShift
                     (EqcCongWeaken (EqcRefl ntnb) (EqhSym bsSubsta))
                     (EqtRefl stn)

      depsa    <- getSortNamespaceDependencies stna
      deps     <- getSortNamespaceDependencies stn
      if | ntna == ntnb && ntna `elem` deps        -> toTerm (eqtSimplify proof0)
         ---
         | ntna /= ntnb && ntnb `elem` depsa
                        && ntna `elem` deps
                        && ntnb `elem` deps        -> toTerm (eqtSimplify proof0)
         | ntna /= ntnb && ntnb `elem` depsa
                        && ntna `notElem` deps
                        && ntnb `elem` deps        -> toTerm (eqtSimplify proof2)
         ---
         | ntna /= ntnb && ntnb `notElem` depsa
                        && ntna `elem` deps
                        && ntnb `elem` deps        -> toTerm (eqtSimplify proof3)
         | ntna /= ntnb && ntnb `notElem` depsa
                        && ntna `notElem` deps
                        && ntnb `elem` deps        -> toTerm (eqtSimplify proof4)
         | ntna /= ntnb && ntnb `notElem` depsa
                        && ntna `elem` deps
                        && ntnb `notElem` deps     -> toTerm (eqtSimplify proof5)
         | otherwise                               -> pure Coq.eqRefl
