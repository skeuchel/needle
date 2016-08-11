{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}

module KnotCore.Elaboration.Interaction.SubstShiftReflectionInd where

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
        sa      <- freshSortVariable stna

        sortDeclGroup ntna k sa sdg
    | sdg@(SortGroupDecl _ _ ntns _) <- sdgs,
      ntna <- ntns
    ]

sortDeclGroup :: forall m. Elab m => NamespaceTypeName ->
  HVarlistVar -> SortVariable -> SortGroupDecl -> m Sentence
sortDeclGroup ntna k sa sgd = do
  binders <- sequenceA [toBinder k, toBinder sa]
  termInduction
    (idLemmaSubstShiftReflectionInd ntna) binders
     goal proofVar proofField (sgSorts sgd)

  where
    goal :: SortVariable -> m Term
    goal sv = do
      let left    = SSubst (TWeaken (T0 ntna) (HVVar k)) (SVar sa)
                      (SShift (CWeaken (C0 ntna) (HVVar k)) (SVar sv))
          right   = SVar sv

      Coq.eq <$> toTerm left <*> toTerm right

    proofVar :: CtorName -> IndexVar -> m Term
    proofVar _cn x =
      if ntna == typeNameOf x
        then
          Coq.TermApp
            <$> (idLemmaSubstIndexShiftIndexReflectionInd ntna >>= toRef)
            <*> sequenceA [toRef sa, toRef k, toRef x]
        else
          pure Coq.eqRefl


    proofField :: BindSpec -> SortVariable -> m Term
    proofField bs sv = do
      let stn = typeNameOf sv
          stna = typeNameOf sa
          ebs = evalBindSpec HV0 bs

      ih <- Coq.TermApp
            <$> (idLemmaSubstShiftReflectionInd ntna stn >>= toRef)
            <*> sequenceA
                [ toRef sv
                , toTerm (HVAppend (HVVar k) ebs)
                , toRef sa
                ]

      bsShifta <- EqhCongAppend (EqhRefl HV0) <$>
                    eqhvlEvalBindspecShift ntna bs
      let proof = foldr1 EqtTrans
                  [ EqtCongSubst
                      (EqxTrans
                         (EqxCongWeaken
                            (EqxRefl ntna)
                            bsShifta)
                         (EqxWeakenAppend (T0 ntna) (HVVar k) ebs))
                      (EqtRefl stna)
                      (EqtCongShift
                         (EqcWeakenAppend (C0 ntna) (HVVar k) ebs)
                         (EqtRefl stn))
                  , EqtAssumption stn ih
                  ]
      deps     <- getSortNamespaceDependencies stn
      if | ntna `elem` deps  -> toTerm (eqtSimplify proof)
         | otherwise         -> pure Coq.eqRefl
