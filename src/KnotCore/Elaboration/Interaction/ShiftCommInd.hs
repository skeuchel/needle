{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}

module KnotCore.Elaboration.Interaction.ShiftCommInd (lemmas) where

import Coq.StdLib as Coq
import Coq.Syntax as Coq

import KnotCore.Syntax
import KnotCore.Elaboration.Core
import KnotCore.Elaboration.Eq
import KnotCore.Elaboration.Interaction.Common

lemmas :: Elab m => [SortGroupDecl] -> m [Sentence]
lemmas sdgs =
  sequenceA
    [ localNames $ do
        k       <- freshHVarlistVar
        cv      <- freshCutoffVar ntn1
        sortDeclGroup ntn1 ntn2 k cv sdg
    | sdg@(SortGroupDecl _ _ ntns _) <- sdgs,
      ntn1 <- ntns,
      ntn2 <- ntns
    ]

sortDeclGroup :: forall m. Elab m => NamespaceTypeName -> NamespaceTypeName ->
  HVarlistVar -> CutoffVar -> SortGroupDecl -> m Sentence
sortDeclGroup ntn1 ntn2 k cv sgd = do
  binders <- sequenceA [toBinder k, toBinder cv]
  termInduction
    (idLemmaShiftCommInd ntn1 ntn2) binders
    goal proofVar proofField (sgSorts sgd)
  where
    goal :: SortVariable -> m Term
    goal sv = do
      let lefthom = SShift
                      (CWeaken (CS (CVar cv)) (HVVar k))
                      (SShift
                         (CWeaken (C0 ntn2) (HVVar k))
                         (SVar sv))
          lefthet = SShift
                      (CWeaken (CVar cv) (HVVar k))
                      (SShift
                         (CWeaken (C0 ntn2) (HVVar k))
                         (SVar sv))
          left    = if ntn1 == ntn2 then lefthom else lefthet
          right   = SShift
                      (CWeaken (C0 ntn2) (HVVar k))
                      (SShift
                         (CWeaken (CVar cv) (HVVar k))
                         (SVar sv))
      Coq.eq <$> toTerm left <*> toTerm right

    proofVar :: CtorName -> IndexVar -> m Term
    proofVar cn x =
      if ntn1 == ntn2 && ntn2 == typeNameOf x
        then Coq.eqFEqual
             <$> toRef cn
             <*> (Coq.TermApp
                  <$> (idLemmaShiftIndexCommInd ntn1 >>= toRef)
                  <*> sequenceA [toRef k, toRef cv, toRef x]
                 )
        else pure Coq.eqRefl

    proofField :: BindSpec -> SortVariable -> m Term
    proofField bs sv = do
      let stn = typeNameOf sv
          ebs = evalBindSpec HV0 bs
      ih <- Coq.TermApp
            <$> (idLemmaShiftCommInd ntn1 ntn2 stn >>= toRef)
            <*> sequenceA
                [ toRef sv
                , toTerm (simplifyHvl $ HVAppend (HVVar k) ebs)
                , toRef cv
                ]

      bsShift1 <- EqhCongAppend (EqhRefl HV0) <$> eqhvlEvalBindspecShift ntn1 bs
      bsShift2 <- EqhCongAppend (EqhRefl HV0) <$> eqhvlEvalBindspecShift ntn2 bs
      let
          proof0 = foldr1 EqtTrans
            [ EqtCongShift
                (EqcTrans
                   (EqcCongWeaken (EqcRefl ntn1) bsShift2)
                   (EqcWeakenAppend (CS (CVar cv)) (HVVar k) ebs)
                )
                (EqtCongShift (EqcWeakenAppend (C0 ntn2) (HVVar k) ebs) (EqtRefl stn))
            , EqtAssumption stn ih
            , EqtSym $
              EqtCongShift
                (EqcTrans
                   (EqcCongWeaken (EqcRefl ntn2) bsShift1)
                   (EqcWeakenAppend (C0 ntn2) (HVVar k) ebs)
                )
                (EqtCongShift (EqcWeakenAppend (CVar cv) (HVVar k) ebs) (EqtRefl stn))
            ]
          proof1 = foldr1 EqtTrans
            [ EqtCongShift
                (EqcTrans
                   (EqcCongWeaken (EqcRefl ntn1) bsShift2)
                   (EqcWeakenAppend (CVar cv) (HVVar k) ebs)
                )
                (EqtCongShift (EqcWeakenAppend (C0 ntn2) (HVVar k) ebs) (EqtRefl stn))
            , EqtAssumption stn ih
            , EqtSym $
              EqtCongShift
                (EqcTrans
                   (EqcCongWeaken (EqcRefl ntn2) bsShift1)
                   (EqcWeakenAppend (C0 ntn2) (HVVar k) ebs)
                )
                (EqtCongShift (EqcWeakenAppend (CVar cv) (HVVar k) ebs) (EqtRefl stn))
            ]
          proof2 =
            EqtCongShift
              (EqcCongWeaken (EqcRefl ntn1) bsShift2)
              (EqtRefl stn)
          proof3 =
            EqtSym $
            EqtCongShift
              (EqcCongWeaken (EqcRefl ntn2) bsShift1)
              (EqtRefl stn)

      deps <- getSortNamespaceDependencies stn
      if | ntn1 == ntn2 && ntn1 `elem` deps     -> toTerm (eqtSimplify proof0)
         | ntn1 `elem` deps && ntn2 `elem` deps -> toTerm (eqtSimplify proof1)
         | ntn1 `elem` deps                     -> toTerm (eqtSimplify proof2)
         | ntn2 `elem` deps                     -> toTerm (eqtSimplify proof3)
         | otherwise                            -> pure Coq.eqRefl
