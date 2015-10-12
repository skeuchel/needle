
module KnotCore.Elaboration.Lemma.SubstShiftCommInd2 where

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
    (idGroupLemmaSubstShiftCommInd ntna ntnb)
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
       then Just <$> idLemmaSubstShiftCommInd ntna ntnb stn
       else return Nothing

sortDeclAssertionInd :: Elab m =>
                        NamespaceTypeName ->
                        NamespaceTypeName ->
                        SubtreeVar ->
                        m Coq.Term
sortDeclAssertionInd ntna ntnb t = localNames $ do

  (stna,_) <- getNamespaceCtor ntna
  depsa    <- getSortNamespaceDependencies stna

  k       <- freshHVarlistVar
  xa      <- freshTraceVar ntna
  ta      <- freshSubtreeVar stna

  let -- α ≡ β \/ α ≢ β, β ∈ α:
      left1  = SSubst (TWeaken (TS ntnb (TVar xa)) (HVVar k)) (SVar ta)
                 (SShift (CWeaken (C0 ntnb) (HVVar k)) (SVar t))
      -- α ≢ β, β ∉ α:
      left2  = SSubst (TWeaken (TVar xa) (HVVar k)) (SVar ta)
                 (SShift (CWeaken (C0 ntnb) (HVVar k)) (SVar t))
      left  | ntnb == ntna      = left1
            | ntnb `elem` depsa = left1
            | otherwise         = left2
      right  = SShift (CWeaken (C0 ntnb) (HVVar k))
                 (SSubst (TWeaken (TVar xa) (HVVar k)) (SVar ta) (SVar t))

  Coq.TermForall
    <$> sequence [toBinder k, toBinder xa, toBinder ta]
    <*> (Coq.eq <$> toTerm left <*> toTerm right)

ctorVarProof :: Elab m =>
  NamespaceTypeName -> NamespaceTypeName ->
  CtorName -> IndexVar -> m Coq.Term
ctorVarProof ntna ntnb _ x = do

  (stna,_) <- getNamespaceCtor ntna
  depsa    <- getSortNamespaceDependencies stna

  k       <- freshHVarlistVar
  xa      <- freshTraceVar ntna
  ta      <- freshSubtreeVar stna

  init <-
    Coq.TermAbs
    <$> sequence [toBinder k, toBinder xa, toBinder ta]

  proof <-
    if ntna == typeNameOf x && ntnb `elem` depsa
    then
      Coq.TermApp
        <$> (idLemmaSubstShiftIndexCommInd ntna ntnb >>= toRef)
        <*> sequence [toRef xa, toRef ta, toRef k, toRef x]
    else
      pure Coq.eqRefl

  return (init proof)

ctorTermProof :: Elab m =>
  NamespaceTypeName -> NamespaceTypeName ->
  m (Coq.Binders, ProofSubtree m)
ctorTermProof ntna ntnb = localNames $ do

  (stna,_) <- getNamespaceCtor ntna

  k       <- freshHVarlistVar
  xa      <- freshTraceVar ntna
  ta      <- freshSubtreeVar stna

  binders <- sequence [toBinder k, toBinder xa, toBinder ta]
  return (binders, fieldDecl ntna ntnb k xa ta)

fieldDecl :: Elab m =>
  NamespaceTypeName -> NamespaceTypeName ->
  HVarlistVar  -> TraceVar -> SubtreeVar ->
  SubtreeVar -> BindSpec -> Hypothesis -> m Coq.Term
fieldDecl ntna ntnb k xa ta sv bs ih = do

  let ebs = evalBindSpec bs
  ih' <- Coq.TermApp
         <$> toRef ih
         <*> sequence
             [ toTerm (simplifyHvl $ HVAppend (HVVar k) ebs),
               toRef xa,
               toRef ta
             ]

  bsSubsta <- eqhvlEvalBindspecSubst ntna bs
  bsShiftb <- eqhvlEvalBindspecShift ntnb bs
  let stn  = typeNameOf sv
      stna = typeNameOf ta
      -- shift_subst0_hom_comm
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
               , EqtAssumption stn ih'
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
               , EqtAssumption stn ih'
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

  (stna,_) <- getNamespaceCtor ntna
  depsa    <- getSortNamespaceDependencies stna
  deps     <- getSortNamespaceDependencies stn
  case () of
   _---
    | ntna == ntnb && ntna `elem` deps        -> toTerm (eqtSimplify proof0)
    ---
    | ntna /= ntnb && ntnb `elem` depsa
                   && ntna `elem` deps
                   && ntnb `elem` deps        -> toTerm (eqtSimplify proof0)
    | ntna /= ntnb && ntnb `elem` depsa
                   && not (ntna `elem` deps)
                   && ntnb `elem` deps        -> toTerm (eqtSimplify proof2)
    ---
    | ntna /= ntnb && not (ntnb `elem` depsa)
                   && ntna `elem` deps
                   && ntnb `elem` deps        -> toTerm (eqtSimplify proof3)
    | ntna /= ntnb && not (ntnb `elem` depsa)
                   && not (ntna `elem` deps)
                   && ntnb `elem` deps        -> toTerm (eqtSimplify proof4)
    | ntna /= ntnb && not (ntnb `elem` depsa)
                   && ntna `elem` deps
                   && not (ntnb `elem` deps)  -> toTerm (eqtSimplify proof5)
    | otherwise                               -> pure Coq.eqRefl
