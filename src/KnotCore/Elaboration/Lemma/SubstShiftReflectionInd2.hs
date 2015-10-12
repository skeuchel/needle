
module KnotCore.Elaboration.Lemma.SubstShiftReflectionInd2 where

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
    [ sortDeclGroup ntna sdg
    | sdg@(SortGroupDecl _ _ ntns _) <- sdgs,
      ntna <- ntns
    ]

sortDeclGroup :: Elab m =>
  NamespaceTypeName -> SortGroupDecl ->
  m [Coq.Sentence]
sortDeclGroup ntna =
  mutualInduction2
    (idGroupLemmaSubstShiftReflectionInd ntna)
    (lemmaIdentifier ntna)
    (sortDeclAssertionInd ntna)
    (ctorVarProof ntna)
    (ctorTermProof ntna)

lemmaIdentifier ::
  Elab m =>
  NamespaceTypeName ->
  SortTypeName ->
  m (Maybe Coq.Identifier)
lemmaIdentifier ntna stn =
  do
    deps <- getSortNamespaceDependencies stn
    if (ntna `elem` deps)
       then Just <$> idLemmaSubstShiftReflectionInd ntna stn
       else return Nothing

sortDeclAssertionInd :: Elab m =>
                        NamespaceTypeName ->
                        SubtreeVar ->
                        m Coq.Term
sortDeclAssertionInd ntna t = localNames $ do

  (stna,_) <- getNamespaceCtor ntna

  k       <- freshHVarlistVar
  s       <- freshSubtreeVar stna

  let left    = SSubst (TWeaken (T0 ntna) (HVVar k)) (SVar s)
                  (SShift (CWeaken (C0 ntna) (HVVar k)) (SVar t))
      right   = SVar t

  Coq.TermForall
    <$> sequence [toBinder k, toBinder s]
    <*> (Coq.eq <$> toTerm left <*> toTerm right)

ctorVarProof :: Elab m =>
  NamespaceTypeName ->
  CtorName -> IndexVar -> m Coq.Term
ctorVarProof ntna _ x = do

  (stna,_) <- getNamespaceCtor ntna

  k       <- freshHVarlistVar
  s       <- freshSubtreeVar stna

  init <-
    Coq.TermAbs
    <$> sequence [toBinder k, toBinder s]

  proof <-
    if ntna == typeNameOf x
    then
      Coq.TermApp
        <$> (idLemmaSubstIndexShiftIndexReflectionInd ntna >>= toRef)
        <*> sequence [toRef s, toRef k, toRef x]
    else
      pure Coq.eqRefl

  return (init proof)

ctorTermProof :: Elab m => NamespaceTypeName -> m (Coq.Binders, ProofSubtree m)
ctorTermProof ntna = localNames $ do

  (stna,_) <- getNamespaceCtor ntna

  k       <- freshHVarlistVar
  s       <- freshSubtreeVar stna

  binders <- sequence [toBinder k, toBinder s]
  return (binders, fieldDecl ntna k s)

fieldDecl :: Elab m =>
  NamespaceTypeName -> HVarlistVar  -> SubtreeVar ->
  SubtreeVar -> BindSpec -> Hypothesis -> m Coq.Term
fieldDecl ntna k sa sv bs ih = do

  let ebs = evalBindSpec bs
  ih' <- Coq.TermApp
         <$> toRef ih
         <*> sequence
             [ toTerm (simplifyHvl $ HVAppend (HVVar k) ebs),
               toRef sa
             ]

  bsShifta <- eqhvlEvalBindspecShift ntna bs
  let stn  = typeNameOf sv
      stna = typeNameOf sa
      -- shift_subst0_hom_comm
      proof = foldr1 EqtTrans
              [ EqtCongSubst
                  (EqxTrans
                     (EqxCongWeaken (EqxRefl ntna) bsShifta)
                     (EqxWeakenAppend (T0 ntna) (HVVar k) ebs))
                  (EqtRefl stna)
                  (EqtCongShift
                     (EqcWeakenAppend (C0 ntna) (HVVar k) ebs)
                     (EqtRefl stn))
              , EqtAssumption stn ih'
              ]
  deps     <- getSortNamespaceDependencies stn
  case () of
   _ | ntna `elem` deps  -> toTerm (eqtSimplify proof)
     | otherwise         -> pure Coq.eqRefl
