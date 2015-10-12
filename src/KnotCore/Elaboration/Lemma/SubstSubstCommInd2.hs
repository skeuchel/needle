
module KnotCore.Elaboration.Lemma.SubstSubstCommInd2 where

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
    (idGroupLemmaSubstSubstCommInd ntna ntnb)
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
       then Just <$> idLemmaSubstSubstCommInd ntna ntnb stn
       else return Nothing

sortDeclAssertionInd :: Elab m =>
                        NamespaceTypeName ->
                        NamespaceTypeName ->
                        SubtreeVar ->
                        m Coq.Term
sortDeclAssertionInd ntna ntnb t = localNames $ do

  stna    <- getSortOfNamespace ntna
  stnb    <- getSortOfNamespace ntnb
  depsa   <- getSortNamespaceDependencies stna
  depsb   <- getSortNamespaceDependencies stnb

  k       <- freshHVarlistVar
  xa      <- freshTraceVar ntna
  ta      <- freshSubtreeVar stna
  tb      <- freshSubtreeVar stnb

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
            | not ainb && not bina = right4

  Coq.TermForall
    <$> sequence [toBinder k, toBinder xa, toBinder ta, toBinder tb]
    <*> (Coq.eq <$> toTerm left <*> toTerm right)

ctorVarProof :: Elab m =>
  NamespaceTypeName -> NamespaceTypeName ->
  CtorName -> IndexVar -> m Coq.Term
ctorVarProof ntna ntnb _ x = do

  stna    <- getSortOfNamespace ntna
  stnb    <- getSortOfNamespace ntnb

  k       <- freshHVarlistVar
  xa      <- freshTraceVar ntna
  ta      <- freshSubtreeVar stna
  tb      <- freshSubtreeVar stnb

  init <-
    Coq.TermAbs
    <$> sequence [toBinder k, toBinder xa, toBinder ta, toBinder tb]

  proof <-
    if typeNameOf x == ntnb
    then Coq.TermApp
         <$> (idLemmaSubstSubstIndexCommRightInd ntna ntnb >>= toRef)
         <*> sequence [toRef xa, toRef ta, toRef tb, toRef k, toRef x]
    else if typeNameOf x == ntna
    then Coq.TermApp
         <$> (idLemmaSubstSubstIndexCommLeftInd ntna ntnb >>= toRef)
         <*> sequence [toRef xa, toRef ta, toRef tb, toRef k, toRef x]
    else pure Coq.eqRefl

  return (init proof)

ctorTermProof :: Elab m =>
  NamespaceTypeName -> NamespaceTypeName ->
  m (Coq.Binders, ProofSubtree m)
ctorTermProof ntna ntnb = localNames $ do

  stna    <- getSortOfNamespace ntna
  stnb    <- getSortOfNamespace ntnb

  k       <- freshHVarlistVar
  xa      <- freshTraceVar ntna
  ta      <- freshSubtreeVar stna
  tb      <- freshSubtreeVar stnb

  binders <- sequence [toBinder k, toBinder xa, toBinder ta, toBinder tb]
  return (binders, fieldDecl ntna ntnb k xa ta tb)

fieldDecl :: Elab m =>
  NamespaceTypeName -> NamespaceTypeName ->
  HVarlistVar  -> TraceVar -> SubtreeVar -> SubtreeVar ->
  SubtreeVar -> BindSpec -> Hypothesis -> m Coq.Term
fieldDecl ntna ntnb k xa ta tb sv bs ih = do

  let ebs = evalBindSpec bs
  ih' <- Coq.TermApp
         <$> toRef ih
         <*> sequence
             [ toTerm (simplifyHvl $ HVAppend (HVVar k) ebs),
               toRef xa,
               toRef ta,
               toRef tb
             ]

  bsSubsta <- eqhvlEvalBindspecSubst ntna bs
  bsSubstb <- eqhvlEvalBindspecSubst ntnb bs
  let stn  = typeNameOf sv
      stna = typeNameOf ta
      stnb = typeNameOf tb
      -- 1. α ∈ β, β ∈ α
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
               , EqtAssumption stn ih'
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
                , EqtAssumption stn ih'
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
                , EqtAssumption stn ih'
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
                 , EqtAssumption stn ih'
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

  (stna,_) <- getNamespaceCtor ntna
  depsa    <- getSortNamespaceDependencies stna
  depsb    <- getSortNamespaceDependencies stna
  deps     <- getSortNamespaceDependencies stn

  let ainb = ntna `elem` depsb
      bina = ntnb `elem` depsa
      ains = ntna `elem` deps
      bins = ntnb `elem` deps

  case () of
   _ | ainb && bina && ains && bins             -> toTerm (eqtSimplify proof1)
     | ainb && not bina && ains && bins         -> toTerm (eqtSimplify proof21)
     | ainb && not bina && ains && not bins     -> toTerm (eqtSimplify proof22)
     | not ainb && bina && ains && bins         -> toTerm (eqtSimplify proof31)
     | not ainb && bina && not ains && bins     -> toTerm (eqtSimplify proof32)
     | not ainb && not bina && ains && bins     -> toTerm (eqtSimplify proof41)
     | not ainb && not bina && ains && not bins -> toTerm (eqtSimplify proof42)
     | not ainb && not bina && not ains && bins -> toTerm (eqtSimplify proof43)
     | otherwise                                -> pure Coq.eqRefl
