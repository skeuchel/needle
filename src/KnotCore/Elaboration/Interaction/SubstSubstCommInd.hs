{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}

module KnotCore.Elaboration.Interaction.SubstSubstCommInd where

import Coq.StdLib as Coq hiding (not)
import Coq.Syntax as Coq

import KnotCore.Syntax
import KnotCore.Elaboration.Core
import KnotCore.Elaboration.Eq
import KnotCore.Elaboration.Interaction.Common

lemmas :: Elab m => [SortGroupDecl] -> m [Coq.Sentence]
lemmas sdgs =
  sequenceA
    [ localNames $ do
        stna    <- getSortOfNamespace ntna
        stnb    <- getSortOfNamespace ntnb
        k       <- freshHVarlistVar
        xa      <- freshTraceVar ntna
        ta      <- freshSortVariable stna
        tb      <- freshSortVariable stnb

        sortDeclGroup ntna ntnb k xa ta tb sdg
    | sdg@(SortGroupDecl _ _ ntns _) <- sdgs
    , ntna <- ntns
    , ntnb <- ntns
    ]

sortDeclGroup :: forall m. Elab m => NamespaceTypeName -> NamespaceTypeName ->
  HVarlistVar -> TraceVar -> SortVariable -> SortVariable -> SortGroupDecl -> m Sentence
sortDeclGroup ntna ntnb k xa ta tb sgd = do
  binders <- sequenceA [toBinder k, toBinder xa, toBinder ta, toBinder tb]
  termInduction
    (idLemmaSubstSubstCommInd ntna ntnb) binders
    goal proofVar proofField (sgSorts sgd)
  where
    goal :: SortVariable -> m Term
    goal t = do

      depsa   <- getSortNamespaceDependencies (typeNameOf ta)
      depsb   <- getSortNamespaceDependencies (typeNameOf tb)

      let left    = SSubst (TWeaken (TVar xa) (HVVar k)) (SVar ta)                              (SSubst (TWeaken (T0 ntnb) (HVVar k)) (SVar tb) (SVar t))
          -- 1. α ∈ β, β ∈ α
          right1  = SSubst (TWeaken (T0 ntnb) (HVVar k)) (SSubst (TVar xa) (SVar ta) (SVar tb)) (SSubst (TWeaken (TS ntnb (TVar xa)) (HVVar k)) (SVar ta) (SVar t))
          -- 2. α ∈ β, β ∉ α
          right2  = SSubst (TWeaken (T0 ntnb) (HVVar k)) (SSubst (TVar xa) (SVar ta) (SVar tb)) (SSubst (TWeaken (TVar xa)           (HVVar k)) (SVar ta) (SVar t))
          -- 3. α ∉ β, β ∈ α
          right3  = SSubst (TWeaken (T0 ntnb) (HVVar k)) (SVar tb)                              (SSubst (TWeaken (TS ntnb (TVar xa)) (HVVar k)) (SVar ta) (SVar t))
          -- 4. α ∉ β, β ∉ α
          right4  = SSubst (TWeaken (T0 ntnb) (HVVar k)) (SVar tb)                              (SSubst (TWeaken (TVar xa)           (HVVar k)) (SVar ta) (SVar t))

          ainb    = ntna `elem` depsb
          bina    = ntnb `elem` depsa

          right |     ainb &&     bina = right1
                |     ainb && not bina = right2
                | not ainb &&     bina = right3
                | otherwise            = right4

      Coq.eq <$> toTerm left <*> toTerm right

    proofVar :: CtorName -> IndexVar -> m Term
    proofVar _ x =
      if typeNameOf x == ntnb
        then Coq.TermApp
             <$> (idLemmaSubstSubstIndexCommRightInd ntna ntnb >>= toRef)
             <*> sequenceA [toRef xa, toRef ta, toRef tb, toRef k, toRef x]
        else if typeNameOf x == ntna
        then Coq.TermApp
             <$> (idLemmaSubstSubstIndexCommLeftInd ntna ntnb >>= toRef)
             <*> sequenceA [toRef xa, toRef ta, toRef tb, toRef k, toRef x]
        else pure Coq.eqRefl

    proofField :: BindSpec -> SortVariable -> m Term
    proofField bs sv = do
      let stn = typeNameOf sv
          ebs = evalBindSpec HV0 bs
          stna = typeNameOf ta
          stnb = typeNameOf tb
      ih <- Coq.TermApp
            <$> (idLemmaSubstSubstCommInd ntna ntnb stn >>= toRef)
            <*> sequenceA
                [ toRef sv
                , toTerm (simplifyHvl $ HVAppend (HVVar k) ebs)
                , toRef xa
                , toRef ta
                , toRef tb
                ]

      bsSubsta <- EqhCongAppend (EqhRefl HV0) <$> eqhvlEvalBindspecSubst ntna bs
      bsSubstb <- EqhCongAppend (EqhRefl HV0) <$> eqhvlEvalBindspecSubst ntnb bs
      let -- 1. α ∈ β, β ∈ α
          proof1 = foldr1 EqtTrans
                   [ EqtCongSubst
                       (EqxTrans
                          (EqxCongWeaken (EqxRefl ntna) bsSubstb)
                          (EqxWeakenAppend (TVar xa) (HVVar k) ebs))
                       (EqtRefl stna)
                       (EqtCongSubst
                          (EqxWeakenAppend (T0 ntnb) (HVVar k) ebs)
                          (EqtRefl stnb)
                          (EqtRefl stn))
                   , EqtAssumption stn ih
                   , EqtSym $
                       EqtCongSubst
                         (EqxTrans
                            (EqxCongWeaken (EqxRefl ntnb) bsSubsta)
                            (EqxWeakenAppend (T0 ntnb) (HVVar k) ebs))
                         (EqtRefl stnb)
                         (EqtCongSubst
                            (EqxWeakenAppend (TS ntnb (TVar xa)) (HVVar k) ebs)
                            (EqtRefl stna)
                            (EqtRefl stn))
                   ]
          -- 2. α ∈ β, β ∉ α
          -- 2.1. α ∈ stn, β ∈ stn
          proof21 = foldr1 EqtTrans
                    [ EqtCongSubst
                        (EqxTrans
                           (EqxCongWeaken (EqxRefl ntna) bsSubstb)
                           (EqxWeakenAppend (TVar xa) (HVVar k) ebs))
                        (EqtRefl stna)
                        (EqtCongSubst
                           (EqxWeakenAppend (T0 ntnb) (HVVar k) ebs)
                           (EqtRefl stnb)
                           (EqtRefl stn))
                    , EqtAssumption stn ih
                    , EqtSym $
                        EqtCongSubst
                           (EqxTrans
                              (EqxCongWeaken (EqxRefl ntnb) bsSubsta)
                              (EqxWeakenAppend (T0 ntnb) (HVVar k) ebs))
                           (EqtRefl stnb)
                           (EqtCongSubst
                              (EqxWeakenAppend (TVar xa) (HVVar k) ebs)
                              (EqtRefl stna)
                              (EqtRefl stn))
                      ]
          -- 2.2. α ∈ stn, β ∉ stn
          proof22 = EqtCongSubst
                      (EqxCongWeaken (EqxRefl ntna) bsSubstb)
                      (EqtRefl stna) (EqtRefl stn)
          -- 3. α ∉ β, β ∈ α
          -- 3.1. α ∈ stn, β ∈ stn
          proof31 = foldr1 EqtTrans
                    [ EqtCongSubst
                        (EqxTrans
                           (EqxCongWeaken (EqxRefl ntna) bsSubstb)
                           (EqxWeakenAppend (TVar xa) (HVVar k) ebs))
                        (EqtRefl stna)
                        (EqtCongSubst
                           (EqxWeakenAppend (T0 ntnb) (HVVar k) ebs)
                           (EqtRefl stnb)
                           (EqtRefl stn))
                    , EqtAssumption stn ih
                    , EqtSym $
                        EqtCongSubst
                          (EqxTrans
                             (EqxCongWeaken (EqxRefl ntnb) bsSubsta)
                             (EqxWeakenAppend (T0 ntnb) (HVVar k) ebs))
                          (EqtRefl stnb)
                          (EqtCongSubst
                             (EqxWeakenAppend (TS ntnb (TVar xa)) (HVVar k) ebs)
                             (EqtRefl stna)
                             (EqtRefl stn))
                    ]
          -- 3.2. α ∉ stn, β ∈ stn
          proof32 = EqtSym $
                      EqtCongSubst
                        (EqxCongWeaken (EqxRefl ntnb) bsSubsta)
                        (EqtRefl stnb)
                        (EqtRefl stn)
          -- 4. α ∉ β, β ∉ α
          -- 4.1. α ∈ stn, β ∈ stn
          proof41 = foldr1 EqtTrans
                    [ EqtCongSubst
                        (EqxTrans
                           (EqxCongWeaken (EqxRefl ntna) bsSubstb)
                           (EqxWeakenAppend (TVar xa) (HVVar k) ebs))
                        (EqtRefl stna)
                        (EqtCongSubst
                           (EqxWeakenAppend (T0 ntnb) (HVVar k) ebs)
                           (EqtRefl stnb)
                           (EqtRefl stn))
                     , EqtAssumption stn ih
                     , EqtSym $
                         EqtCongSubst
                           (EqxTrans
                              (EqxCongWeaken (EqxRefl ntnb) bsSubsta)
                              (EqxWeakenAppend (T0 ntnb) (HVVar k) ebs))
                           (EqtRefl stnb)
                           (EqtCongSubst
                              (EqxWeakenAppend (TVar xa) (HVVar k) ebs)
                              (EqtRefl stna)
                              (EqtRefl stn))
                     ]
          -- 4.2. α ∈ stn, β ∉ stn
          proof42 = EqtCongSubst
                      (EqxCongWeaken (EqxRefl ntna) bsSubstb)
                      (EqtRefl stna) (EqtRefl stn)
          -- 4.3. α ∉ stn, β ∈ stn
          proof43 = EqtSym $
                      EqtCongSubst
                        (EqxCongWeaken (EqxRefl ntnb) bsSubsta)
                        (EqtRefl stnb)
                        (EqtRefl stn)

      depsa    <- getSortNamespaceDependencies stna
      depsb    <- getSortNamespaceDependencies stna
      deps     <- getSortNamespaceDependencies stn

      let ainb = ntna `elem` depsb
          bina = ntnb `elem` depsa
          ains = ntna `elem` deps
          bins = ntnb `elem` deps

      if | ainb && bina && ains && bins             -> toTerm (eqtSimplify proof1)
         | ainb && not bina && ains && bins         -> toTerm (eqtSimplify proof21)
         | ainb && not bina && ains && not bins     -> toTerm (eqtSimplify proof22)
         | not ainb && bina && ains && bins         -> toTerm (eqtSimplify proof31)
         | not ainb && bina && not ains && bins     -> toTerm (eqtSimplify proof32)
         | not ainb && not bina && ains && bins     -> toTerm (eqtSimplify proof41)
         | not ainb && not bina && ains && not bins -> toTerm (eqtSimplify proof42)
         | not ainb && not bina && not ains && bins -> toTerm (eqtSimplify proof43)
         | otherwise                                -> pure Coq.eqRefl
