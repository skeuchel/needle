{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}

module KnotCore.Elaboration.Interaction.SubstSubordInd where

import Coq.StdLib as Coq
import Coq.Syntax as Coq

import KnotCore.Syntax
import KnotCore.Elaboration.Core
import KnotCore.Elaboration.Eq ()
import KnotCore.Elaboration.Interaction.Common

lemmas :: Elab m => [SortGroupDecl] -> m [Coq.Sentence]
lemmas sgds = do
  ntns <- getNamespaces
  concat <$>
    sequenceA
      [ do
          (stna,_) <- getNamespaceCtor ntna
          depsa <- getSortNamespaceDependencies stna
          sequenceA
            [ localNames $ do
                k       <- freshHVarlistVar
                xa      <- freshTraceVar ntna
                ta      <- freshSortVariable stna
                sortDeclGroup ntna ntnb k xa ta sgd
            | ntnb <- ntns, ntnb `notElem` depsa
            ]
      | sgd@(SortGroupDecl _ _ deps _) <- sgds,
        ntna <- deps
      ]

sortDeclGroup :: forall m. Elab m => NamespaceTypeName -> NamespaceTypeName ->
  HVarlistVar -> TraceVar -> SortVariable -> SortGroupDecl -> m Sentence
sortDeclGroup ntna ntnb k xa ta sgd = do
  binders <- sequenceA [toBinder k, toBinder xa, toBinder ta]
  termInduction
    (idLemmaSubstSubordInd ntna ntnb) binders
    goal proofVar proofField (sgSorts sgd)
  where
    goal :: SortVariable -> m Term
    goal t = do

      let left   = SSubst (TWeaken (TS ntnb (TVar xa)) (HVVar k)) (SVar ta) (SVar t)
          right  = SSubst (TWeaken (TVar xa) (HVVar k)) (SVar ta) (SVar t)

      Coq.eq <$> toTerm left <*> toTerm right

    proofVar :: CtorName -> IndexVar -> m Term
    proofVar _ x =
      if ntna == typeNameOf x
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
            <$> (idLemmaSubstSubordInd ntna ntnb stn >>= toRef)
            <*> sequenceA
                [ toRef sv
                , toTerm (simplifyHvl $ HVAppend (HVVar k) ebs)
                , toRef xa
                , toRef ta
                ]

      let proof = foldr1 EqtTrans
                  [ EqtCongSubst
                      (EqxWeakenAppend (TS ntnb (TVar xa)) (HVVar k) ebs)
                      (EqtRefl stna) (EqtRefl stn)
                  , EqtAssumption stn ih
                  , EqtCongSubst
                      (EqxSym (EqxWeakenAppend (TVar xa) (HVVar k) ebs))
                      (EqtRefl stna)
                      (EqtRefl stn)
                  ]

      deps     <- getSortNamespaceDependencies stn

      if ntna `elem` deps
         then toTerm proof
         else pure Coq.eqRefl
