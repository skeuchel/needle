{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}

module KnotCore.Elaboration.Interaction.ShiftSubstCommInd (lemmas) where

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
        (stnb,_) <- getNamespaceCtor ntnb
        k       <- freshHVarlistVar
        ca      <- freshCutoffVar ntna
        tb      <- freshSortVariable stnb
        sortDeclGroup ntna ntnb k ca tb sdg
    | sdg@(SortGroupDecl _ _ ntns _) <- sdgs,
      ntna <- ntns,
      ntnb <- ntns
    ]

sortDeclGroup :: forall m. Elab m => NamespaceTypeName -> NamespaceTypeName ->
  HVarlistVar -> CutoffVar -> SortVariable -> SortGroupDecl -> m Sentence
sortDeclGroup ntna ntnb k cva tb sgd = do
  binders <- sequenceA [toBinder k, toBinder cva, toBinder tb]
  termInduction
    (idLemmaShiftSubstCommInd ntna ntnb) binders
    goal proofVar proofField (sgSorts sgd)
  where
    goal :: SortVariable -> m Term
    goal sv = do

      depsb    <- getSortNamespaceDependencies (typeNameOf tb)

      let left   = SShift (CWeaken (CVar cva) (HVVar k))
                       (SSubst (TWeaken (T0 ntnb) (HVVar k)) (SVar tb) (SVar sv))
          -- α ≡ β
          right1 = SSubst (TWeaken (T0 ntnb) (HVVar k))
                     (SShift (CVar cva) (SVar tb))
                     (SShift (CWeaken (CS (CVar cva)) (HVVar k)) (SVar sv))
          -- α ≢ β, α ∈ β
          right2 = SSubst (TWeaken (T0 ntnb) (HVVar k))
                     (SShift (CVar cva) (SVar tb))
                     (SShift (CWeaken (CVar cva) (HVVar k)) (SVar sv))
          -- α ≢ β, α ∉ β.
          right3 = SSubst (TWeaken (T0 ntnb) (HVVar k))
                     (SVar tb)
                     (SShift (CWeaken (CVar cva) (HVVar k)) (SVar sv))
          right | ntna == ntnb      = right1
                | ntna `elem` depsb = right2
                | otherwise         = right3

      Coq.eq <$> toTerm left <*> toTerm right

    proofVar :: CtorName -> IndexVar -> m Term
    proofVar _cn x = do

      depsb    <- getSortNamespaceDependencies (typeNameOf tb)
      if ntna `elem` depsb && ntnb == typeNameOf x
        then
          TermApp
            <$> (idLemmaShiftSubstIndexCommInd ntna ntnb >>= toRef)
            <*> sequenceA [toRef cva, toRef tb, toRef k, toRef x]
        else
          pure Coq.eqRefl

    proofField :: BindSpec -> SortVariable -> m Term
    proofField bs sv = do
      let stn = typeNameOf sv
          ebs = evalBindSpec HV0 bs
          stnb = typeNameOf tb

      ih <- TermApp
            <$> (idLemmaShiftSubstCommInd ntna ntnb stn >>= toRef)
            <*> sequenceA
                [ toRef sv
                , toTerm (HVAppend (HVVar k) ebs)
                , toRef cva
                , toRef tb
                ]

      bsShifta <- EqhCongAppend (EqhRefl HV0) <$> eqhvlEvalBindspecShift ntna bs
      bsSubstb <- EqhCongAppend (EqhRefl HV0) <$> eqhvlEvalBindspecSubst ntnb bs
      let -- shift_subst0_hom_comm
          proof0 = foldr1 EqtTrans
                   [ EqtCongShift
                       (EqcTrans
                          (EqcCongWeaken (EqcRefl ntna) bsSubstb)
                          (EqcWeakenAppend (CVar cva) (HVVar k) ebs))
                       (EqtCongSubst
                          (EqxWeakenAppend (T0 ntnb) (HVVar k) ebs)
                          (EqtRefl stnb)
                          (EqtRefl stn))
                   , EqtAssumption stn ih
                   , EqtSym
                       (EqtCongSubst
                          (EqxTrans
                             (EqxCongWeaken (EqxRefl ntnb) bsShifta)
                             (EqxWeakenAppend (T0 ntnb) (HVVar k) ebs))
                          (EqtRefl stnb)
                          (EqtCongShift
                             (EqcWeakenAppend (CS (CVar cva)) (HVVar k) ebs)
                             (EqtRefl stn))
                       )
                   ]
          -- shift_subst0_het_comm1
          proof1 = foldr1 EqtTrans
                   [ EqtCongShift
                      (EqcTrans
                        (EqcCongWeaken (EqcRefl ntna) bsSubstb)
                        (EqcWeakenAppend (CVar cva) (HVVar k) ebs))
                      (EqtCongSubst
                         (EqxWeakenAppend (T0 ntnb) (HVVar k) ebs)
                         (EqtRefl stnb)
                         (EqtRefl stn))
                   , EqtAssumption stn ih
                   , EqtCongSubst
                       (EqxSym (EqxTrans
                                  (EqxCongWeaken (EqxRefl ntna) bsShifta)
                                  (EqxWeakenAppend (T0 ntnb) (HVVar k) ebs)))
                       (EqtRefl stnb)
                       (EqtCongShift
                          (EqcSym (EqcWeakenAppend (CVar cva) (HVVar k) ebs))
                          (EqtRefl stn))
                   ]
          proof2 = EqtCongShift
                    (EqcCongWeaken (EqcRefl ntna) bsSubstb)
                    (EqtRefl stn)
          -- shift_subst0_het_comm2
          proof3 = foldr1 EqtTrans
                   [ EqtCongShift
                       (EqcTrans
                         (EqcCongWeaken (EqcRefl ntna) bsSubstb)
                         (EqcWeakenAppend (CVar cva) (HVVar k) ebs))
                       (EqtCongSubst
                         (EqxWeakenAppend (T0 ntnb) (HVVar k) ebs)
                         (EqtRefl stnb)
                         (EqtRefl stn))
                   , EqtAssumption stn ih
                   , EqtSym
                       (EqtTrans
                         (EqtCongSubst
                           (EqxTrans
                             (EqxCongWeaken (EqxRefl ntnb) bsShifta)
                             (EqxWeakenAppend (T0 ntnb) (HVVar k) ebs))
                           (EqtRefl stnb)
                           (EqtCongShift
                              (EqcWeakenAppend (CVar cva) (HVVar k) ebs)
                              (EqtRefl stn)))
                         (EqtRefl stn))
                   ]
          proof4 = EqtCongShift
                     (EqcCongWeaken (EqcRefl ntna) bsSubstb)
                     (EqtRefl stn)
          proof5 = EqtCongSubst
                     (EqxCongWeaken (EqxRefl ntnb) (EqhSym bsShifta))
                     (EqtRefl stnb)
                     (EqtRefl stn)

      depsb    <- getSortNamespaceDependencies stnb
      deps     <- getSortNamespaceDependencies stn
      if | ntna == ntnb && ntna `elem` deps        -> toTerm (eqtSimplify proof0)
         ---
         | ntna /= ntnb && ntna `elem` depsb
                        && ntna `elem` deps
                        && ntnb `elem` deps        -> toTerm (eqtSimplify proof1)
         | ntna /= ntnb && ntna `elem` depsb
                        && ntna `elem` deps
                        && ntnb `notElem` deps     -> toTerm (eqtSimplify proof2)
         ---
         | ntna /= ntnb && ntna `notElem` depsb
                        && ntna `elem` deps
                        && ntnb `elem` deps        -> toTerm (eqtSimplify proof3)
         | ntna /= ntnb && ntna `notElem` depsb
                        && ntna `elem` deps
                        && ntnb `notElem` deps     -> toTerm (eqtSimplify proof4)
         | ntna /= ntnb && ntna `notElem` depsb
                        && ntna `notElem` deps
                        && ntnb `elem` deps        -> toTerm (eqtSimplify proof5)
         | otherwise                               -> pure Coq.eqRefl
