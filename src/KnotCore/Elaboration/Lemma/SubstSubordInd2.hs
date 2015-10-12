
module KnotCore.Elaboration.Lemma.SubstSubordInd2 where

import Control.Applicative

import qualified Coq.StdLib as Coq
import qualified Coq.Syntax as Coq

import Data.List (nub,(\\))

import KnotCore.Syntax
import KnotCore.Elaboration.Core
import KnotCore.Elaboration.Lemma.Mutual2
import KnotCore.Elaboration.Eq

lemmas :: Elab m => [SortGroupDecl] -> m [Coq.Sentence]
lemmas sdgs = do
  ntns <- getNamespaces
  concat . concat <$>
    sequence
      [ do
          (stna,_) <- getNamespaceCtor ntna
          depsa <- getSortNamespaceDependencies stna
          sequence
            [ sortDeclGroup ntna ntnb sdg
            | ntnb <- ntns \\ depsa
            ]
      | sdg@(SortGroupDecl _ _ deps _) <- sdgs,
        ntna <- deps
      ]

sortDeclGroup :: Elab m =>
  NamespaceTypeName -> NamespaceTypeName -> SortGroupDecl ->
  m [Coq.Sentence]
sortDeclGroup ntna ntnb =
  mutualInduction2
    (idGroupLemmaSubstSubordInd ntna ntnb)
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
    (stna,_) <- getNamespaceCtor ntna
    depsa <- getSortNamespaceDependencies stna

    if (ntna `elem` deps) &&
       (ntnb `notElem` depsa)
       then Just <$> idLemmaSubstSubordInd ntna ntnb stn
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

  let left   = SSubst (TWeaken (TS ntnb (TVar xa)) (HVVar k)) (SVar ta) (SVar t)
      right  = SSubst (TWeaken (TVar xa) (HVVar k)) (SVar ta) (SVar t)

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
    if ntna == typeNameOf x
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
      proof = foldr1 EqtTrans
              [ EqtCongSubst
                  (EqxWeakenAppend (TS ntnb (TVar xa)) (HVVar k) ebs)
                  (EqtRefl stna) (EqtRefl stn)
              , EqtAssumption stn ih'
              , EqtCongSubst
                  (EqxSym (EqxWeakenAppend (TVar xa) (HVVar k) ebs))
                  (EqtRefl stna)
                  (EqtRefl stn)
              ]

  deps     <- getSortNamespaceDependencies stn

  if ntna `elem` deps
     then toTerm (eqtSimplify proof)
     else pure Coq.eqRefl
