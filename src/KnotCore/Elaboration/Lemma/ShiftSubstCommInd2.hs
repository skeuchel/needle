
module KnotCore.Elaboration.Lemma.ShiftSubstCommInd2 where

import Control.Applicative

import qualified Coq.StdLib as Coq
import qualified Coq.Syntax as Coq

import Data.List (nub)

import KnotCore.Syntax
import KnotCore.Elaboration.Core
import KnotCore.Elaboration.Lemma.Mutual2
import KnotCore.Elaboration.Eq

lemmas :: Elab m => [SortGroupDecl] -> m [Coq.Sentence]
lemmas sdgs = concat <$>
  sequence
    [ sortDeclGroup ntna ntnb sdg
    | sdg@(SortGroupDecl _ _ ntns _) <- sdgs,
      ntna <- ntns,
      ntnb <- ntns
    ]

sortDeclGroup :: Elab m =>
  NamespaceTypeName -> NamespaceTypeName -> SortGroupDecl ->
  m [Coq.Sentence]
sortDeclGroup ntna ntnb =
  mutualInduction2
    (idGroupLemmaShiftSubstCommInd ntna ntnb)
    (lemmaIdentifier ntna ntnb)
    (sortDeclAssertionInd ntna ntnb)
    (ctorVarProof ntna ntnb)
    (ctorTermProof ntna ntnb)

lemmaIdentifier ::
  Elab m =>
  NamespaceTypeName ->
  NamespaceTypeName ->
  SortTypeName ->
  m (Maybe Coq.Identifier)
lemmaIdentifier ntna ntnb stn =
  do
    deps <- getSortNamespaceDependencies stn
    if (ntna `elem` deps) && (ntnb `elem` deps)
       then Just <$> idLemmaShiftSubstCommInd ntna ntnb stn
       else return Nothing

sortDeclAssertionInd :: Elab m =>
                        NamespaceTypeName ->
                        NamespaceTypeName ->
                        SubtreeVar ->
                        m Coq.Term
sortDeclAssertionInd ntna ntnb t = localNames $ do

  (stnb,_) <- getNamespaceCtor ntnb
  depsb    <- getSortNamespaceDependencies stnb

  k       <- freshHVarlistVar
  ca      <- freshCutoffVar ntna
  tb      <- freshSubtreeVar stnb

  let left   = SShift (CWeaken (CVar ca) (HVVar k))
                   (SSubst (TWeaken (T0 ntnb) (HVVar k)) (SVar tb) (SVar t))
      -- α ≡ β
      right1 = SSubst (TWeaken (T0 ntnb) (HVVar k))
                 (SShift (CVar ca) (SVar tb))
                 (SShift (CWeaken (CS (CVar ca)) (HVVar k)) (SVar t))
      -- α ≢ β, α ∈ β
      right2 = SSubst (TWeaken (T0 ntnb) (HVVar k))
                 (SShift (CVar ca) (SVar tb))
                 (SShift (CWeaken (CVar ca) (HVVar k)) (SVar t))
      -- α ≢ β, α ∉ β.
      right3 = SSubst (TWeaken (T0 ntnb) (HVVar k))
                 (SVar tb)
                 (SShift (CWeaken (CVar ca) (HVVar k)) (SVar t))
      right | ntna == ntnb      = right1
            | ntna `elem` depsb = right2
            | otherwise         = right3

  Coq.TermForall
    <$> sequence [toBinder k, toBinder ca, toBinder tb]
    <*> (Coq.eq <$> toTerm left <*> toTerm right)

ctorVarProof :: Elab m =>
  NamespaceTypeName -> NamespaceTypeName ->
  CtorName -> IndexVar -> m Coq.Term
ctorVarProof ntna ntnb _ x = do

  (stnb,_) <- getNamespaceCtor ntnb
  depsb    <- getSortNamespaceDependencies stnb

  k       <- freshHVarlistVar
  ca      <- freshCutoffVar ntna
  tb      <- freshSubtreeVar stnb

  init <-
    Coq.TermAbs
    <$> sequence [toBinder k, toBinder ca, toBinder tb]

  proof <-
    if ntna `elem` depsb && ntnb == typeNameOf x
    then
      Coq.TermApp
        <$> (idLemmaShiftSubstIndexCommInd ntna ntnb >>= toRef)
        <*> sequence [toRef ca, toRef tb, toRef k, toRef x]
    else
      pure Coq.eqRefl

  return (init proof)

ctorTermProof :: Elab m =>
  NamespaceTypeName -> NamespaceTypeName ->
  m (Coq.Binders, ProofSubtree m)
ctorTermProof ntna ntnb = localNames $ do

  (stnb,_) <- getNamespaceCtor ntnb

  k       <- freshHVarlistVar
  ca      <- freshCutoffVar ntna
  tb      <- freshSubtreeVar stnb

  binders <- sequence [toBinder k, toBinder ca, toBinder tb]
  return (binders, fieldDecl ntna ntnb k ca tb)

fieldDecl :: Elab m =>
  NamespaceTypeName -> NamespaceTypeName ->
  HVarlistVar  -> CutoffVar -> SubtreeVar ->
  SubtreeVar -> BindSpec -> Hypothesis -> m Coq.Term
fieldDecl ntna ntnb k ca tb sv bs ih = do

  let ebs = evalBindSpec bs
  ih' <- Coq.TermApp
         <$> toRef ih
         <*> sequence
             [ toTerm (simplifyHvl $ HVAppend (HVVar k) ebs),
               toRef ca,
               toRef tb
             ]

  bsShifta <- eqhvlEvalBindspecShift ntna bs
  bsSubstb <- eqhvlEvalBindspecSubst ntnb bs
  let stn  = typeNameOf sv
      stnb = typeNameOf tb
      -- shift_subst0_hom_comm
      proof0 = foldr1 EqtTrans
               [ EqtCongShift
                   (EqcTrans
                      (EqcCongWeaken (EqcRefl ntna) bsSubstb)
                      (EqcWeakenAppend (CVar ca) (HVVar k) ebs))
                   (EqtCongSubst
                      (EqxWeakenAppend (T0 ntnb) (HVVar k) ebs)
                      (EqtRefl stnb)
                      (EqtRefl stn))
               , EqtAssumption stn ih'
               , EqtSym $
                   (EqtCongSubst
                      (EqxTrans
                         (EqxCongWeaken (EqxRefl ntnb) bsShifta)
                         (EqxWeakenAppend (T0 ntnb) (HVVar k) ebs))
                      (EqtRefl stnb)
                      (EqtCongShift
                         (EqcWeakenAppend (CS (CVar ca)) (HVVar k) ebs)
                         (EqtRefl stn))
                   )
               ]
      -- shift_subst0_het_comm1
      proof1 = foldr1 EqtTrans
               [ EqtCongShift
                  (EqcTrans
                    (EqcCongWeaken (EqcRefl ntna) bsSubstb)
                    (EqcWeakenAppend (CVar ca) (HVVar k) ebs))
                  (EqtCongSubst
                     (EqxWeakenAppend (T0 ntnb) (HVVar k) ebs)
                     (EqtRefl stnb)
                     (EqtRefl stn))
               , EqtAssumption stn ih'
               , EqtCongSubst
                   (EqxSym (EqxTrans
                              (EqxCongWeaken (EqxRefl ntna) bsShifta)
                              (EqxWeakenAppend (T0 ntnb) (HVVar k) ebs)))
                   (EqtRefl stnb)
                   (EqtCongShift
                      (EqcSym (EqcWeakenAppend (CVar ca) (HVVar k) ebs))
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
                     (EqcWeakenAppend (CVar ca) (HVVar k) ebs))
                   (EqtCongSubst
                     (EqxWeakenAppend (T0 ntnb) (HVVar k) ebs)
                     (EqtRefl stnb)
                     (EqtRefl stn))
               , EqtAssumption stn ih'
               , EqtSym
                   (EqtTrans
                     (EqtCongSubst
                       (EqxTrans
                         (EqxCongWeaken (EqxRefl ntnb) bsShifta)
                         (EqxWeakenAppend (T0 ntnb) (HVVar k) ebs))
                       (EqtRefl stnb)
                       (EqtCongShift
                          (EqcWeakenAppend (CVar ca) (HVVar k) ebs)
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

  (stnb,_) <- getNamespaceCtor ntnb
  depsb    <- getSortNamespaceDependencies stnb
  deps     <- getSortNamespaceDependencies stn
  case () of
   _---
    | ntna == ntnb && ntna `elem` deps        -> toTerm (eqtSimplify proof0)
    ---
    | ntna /= ntnb && ntna `elem` depsb
                   && ntna `elem` deps
                   && ntnb `elem` deps        -> toTerm (eqtSimplify proof1)
    | ntna /= ntnb && ntna `elem` depsb
                   && ntna `elem` deps
                   && not (ntnb `elem` deps)  -> toTerm (eqtSimplify proof2)
    ---
    | ntna /= ntnb && not (ntna `elem` depsb)
                   && ntna `elem` deps
                   && ntnb `elem` deps        -> toTerm (eqtSimplify proof3)
    | ntna /= ntnb && not (ntna `elem` depsb)
                   && ntna `elem` deps
                   && not (ntnb `elem` deps)  -> toTerm (eqtSimplify proof4)
    | ntna /= ntnb && not (ntna `elem` depsb)
                   && not (ntna `elem` deps)
                   && ntnb `elem` deps        -> toTerm (eqtSimplify proof5)
    | otherwise                               -> pure Coq.eqRefl
