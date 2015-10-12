
module KnotCore.Elaboration.Lemma.ShiftCommInd2 where

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
    [ sortDeclGroup ntn1 ntn2 sdg
    | sdg@(SortGroupDecl _ _ ntns _) <- sdgs,
      ntn1 <- ntns,
      ntn2 <- ntns
    ]

sortDeclGroup :: Elab m =>
  NamespaceTypeName -> NamespaceTypeName -> SortGroupDecl ->
  m [Coq.Sentence]
sortDeclGroup ntn1 ntn2 =
  mutualInduction2
    (idGroupLemmaShiftCommInd ntn1 ntn2)
    (lemmaIdentifier ntn1 ntn2)
    (sortDeclAssertionInd ntn1 ntn2)
    (ctorVarProof ntn1 ntn2)
    (ctorTermProof ntn1 ntn2)

lemmaIdentifier ::
  Elab m =>
  NamespaceTypeName ->
  NamespaceTypeName ->
  SortTypeName ->
  m (Maybe Coq.Identifier)
lemmaIdentifier ntn1 ntn2 stn =
  do
    deps <- getSortNamespaceDependencies stn
    if (ntn1 `elem` deps) && (ntn2 `elem` deps)
       then Just <$> idLemmaShiftCommInd ntn1 ntn2 stn
       else return Nothing

sortDeclAssertionInd :: Elab m =>
                        NamespaceTypeName ->
                        NamespaceTypeName ->
                        SubtreeVar ->
                        m Coq.Term
sortDeclAssertionInd ntn1 ntn2 t = localNames $ do
  k       <- freshHVarlistVar
  c       <- freshCutoffVar ntn1

  let lefthom = SShift
                  (CWeaken (CS (CVar c)) (HVVar k))
                  (SShift
                     (CWeaken (C0 ntn2) (HVVar k))
                     (SVar t))
      lefthet = SShift
                  (CWeaken (CVar c) (HVVar k))
                  (SShift
                     (CWeaken (C0 ntn2) (HVVar k))
                     (SVar t))
      left    = if ntn1 == ntn2 then lefthom else lefthet
      right   = SShift
                  (CWeaken (C0 ntn2) (HVVar k))
                  (SShift
                     (CWeaken (CVar c) (HVVar k))
                     (SVar t))
  Coq.TermForall
    <$> sequence [toBinder k, toBinder c]
    <*> (Coq.eq <$> toTerm left <*> toTerm right)

ctorVarProof :: Elab m =>
  NamespaceTypeName -> NamespaceTypeName ->
  CtorName -> IndexVar -> m Coq.Term
ctorVarProof ntn1 ntn2 cn x = do

  k     <- freshHVarlistVar
  c     <- freshCutoffVar ntn1

  init <-
    Coq.TermAbs
    <$> sequence [toBinder k, toBinder c]

  proof <-
    if ntn1 == ntn2 && ntn2 == typeNameOf x
    then Coq.eqFEqual
         <$> toRef cn
         <*> (Coq.TermApp
              <$> (idLemmaShiftIndexCommInd ntn1 >>= toRef)
              <*> sequence [toRef k, toRef c, toRef x]
             )
    else pure Coq.eqRefl

  return (init proof)

ctorTermProof :: Elab m =>
  NamespaceTypeName -> NamespaceTypeName ->
  m (Coq.Binders, ProofSubtree m)
ctorTermProof ntn1 ntn2 = localNames $ do

  k     <- freshHVarlistVar
  c     <- freshCutoffVar ntn1

  binders <- sequence [toBinder k, toBinder c]
  return (binders, fieldDecl ntn1 ntn2 k c)

fieldDecl :: Elab m =>
  NamespaceTypeName -> NamespaceTypeName ->
  HVarlistVar  -> CutoffVar ->
  SubtreeVar -> BindSpec -> Hypothesis -> m Coq.Term
fieldDecl ntn1 ntn2 k c sv bs ih = do

  let ebs = evalBindSpec bs
  ih' <- Coq.TermApp
         <$> toRef ih
         <*> sequence
             [ toTerm (simplifyHvl $ HVAppend (HVVar k) ebs),
               toRef c
             ]

  bsShift1 <- eqhvlEvalBindspecShift ntn1 bs
  bsShift2 <- eqhvlEvalBindspecShift ntn2 bs
  let stn  = typeNameOf sv
      proof0 = foldr1 EqtTrans
        [ EqtCongShift
            (EqcTrans
               (EqcCongWeaken (EqcRefl ntn1) bsShift2)
               (EqcWeakenAppend (CS (CVar c)) (HVVar k) ebs)
            )
            (EqtCongShift (EqcWeakenAppend (C0 ntn2) (HVVar k) ebs) (EqtRefl stn))
        , EqtAssumption stn ih'
        , EqtSym $
          EqtCongShift
            (EqcTrans
               (EqcCongWeaken (EqcRefl ntn2) bsShift1)
               (EqcWeakenAppend (C0 ntn2) (HVVar k) ebs)
            )
            (EqtCongShift (EqcWeakenAppend (CVar c) (HVVar k) ebs) (EqtRefl stn))
        ]
      proof1 = foldr1 EqtTrans
        [ EqtCongShift
            (EqcTrans
               (EqcCongWeaken (EqcRefl ntn1) bsShift2)
               (EqcWeakenAppend (CVar c) (HVVar k) ebs)
            )
            (EqtCongShift (EqcWeakenAppend (C0 ntn2) (HVVar k) ebs) (EqtRefl stn))
        , EqtAssumption stn ih'
        , EqtSym $
          EqtCongShift
            (EqcTrans
               (EqcCongWeaken (EqcRefl ntn2) bsShift1)
               (EqcWeakenAppend (C0 ntn2) (HVVar k) ebs)
            )
            (EqtCongShift (EqcWeakenAppend (CVar c) (HVVar k) ebs) (EqtRefl stn))
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
  case () of
   _| ntn1 == ntn2 && ntn1 `elem` deps     -> toTerm (eqtSimplify proof0)
    | ntn1 `elem` deps && ntn2 `elem` deps -> toTerm (eqtSimplify proof1)
    | ntn1 `elem` deps                     -> toTerm (eqtSimplify proof2)
    | ntn2 `elem` deps                     -> toTerm (eqtSimplify proof3)
    | otherwise                            -> pure Coq.eqRefl
