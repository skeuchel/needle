
module KnotCore.Elaboration.Lemma.ShiftCommInd where

import Control.Applicative

import qualified Coq.StdLib as Coq
import qualified Coq.Syntax as Coq

import Data.List (nub)

import KnotCore.Syntax
import KnotCore.Elaboration.Core
import KnotCore.Elaboration.Eq
import KnotCore.Elaboration.Lemma.Mutual

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
  mutualInduction
    (idGroupLemmaShiftCommInd ntn1 ntn2)
    (lemmaIdentifier ntn1 ntn2)
    (sortDeclAssertionInd ntn1 ntn2)
    (ctorDecl ntn1 ntn2)

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
                        SortDecl ->
                        m Coq.Term
sortDeclAssertionInd ntn1 ntn2 (SortDecl stn _ _) = localNames $ do
  t       <- freshSubtreeVar stn
  c       <- freshCutoffVar ntn1
  k       <- freshHVarlistVar

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
    <$> sequence [toBinder t, toBinder k, toBinder c]
    <*> (Coq.eq <$> toTerm left <*> toTerm right)

ctorDecl :: Elab m => NamespaceTypeName -> NamespaceTypeName -> ProofCtor m
ctorDecl ntn1 ntn2 (CtorVar cn mv) = do

  k     <- freshHVarlistVar
  x     <- freshIndexVar ntn1
  c     <- freshCutoffVar ntn1

  init <- sequence
          [ Coq.PrIntros <$> sequence [toId x, toId k, toId c]
          ]
  finish <- if ntn1 == ntn2 && ntn2 == typeNameOf mv
              then sequence
                   [ Coq.PrApply
                     <$> (Coq.TermApp
                          <$> pure (Coq.termIdent "f_equal")
                          <*> sequence [toRef cn]
                         ),
                     Coq.PrApply
                     <$> (idLemmaShiftIndexCommInd ntn1 >>= toRef)
                   ]
              else pure
                   [ Coq.PrTactic "reflexivity" []
                   ]
  let proof = init ++ finish
  return (proof, fieldDecl ntn1 ntn2 k c)
ctorDecl ntn1 ntn2 (CtorTerm cn fds) = localNames $ do

  k     <- freshHVarlistVar
  kId   <- toId k
  c     <- freshCutoffVar ntn1
  cId   <- toId c
  cnTm  <- toRef cn

  return
    ([ Coq.PrSeq
       [ Coq.PrIntros [kId, cId],
         Coq.PrSimpl,
         Coq.PrFEqual (length [ () | FieldSubtree{} <- fds ]) cnTm
       ]
     ], fieldDecl ntn1 ntn2 k c)

fieldDecl :: Elab m => NamespaceTypeName -> NamespaceTypeName ->
                       HVarlistVar  -> CutoffVar -> ProofSubtree m
fieldDecl ntn1 ntn2 k c _ bs ih = do

  let fns  = nub [ fn | VleCall _ fn _ <- bs ]
      ntns = nub [ ntn1, ntn2 ]
  let hvl  = HVAppend (HVVar k) (evalBindSpec bs)
  weakenCutoffAppend1 <- idLemmaWeakenCutoffAppend ntn1
  weakenCutoffAppend2 <- idLemmaWeakenCutoffAppend ntn2

  rewrt <- sequence
    [ Coq.PrRepeat . Coq.PrRewrite <$> (idLemmaStabilityShift ntn fn >>= toRef)
    | fn <- fns, ntn <- ntns
    ]

  proof <- sequence
    [ Coq.PrRepeat . Coq.PrRewrite <$> toRef weakenCutoffAppend1,
      Coq.PrRepeat . Coq.PrRewrite <$> toRef weakenCutoffAppend2,
      Coq.PrExact
      <$> (Coq.TermApp
           <$> hypothesisRef ih
           <*> sequence [ toTerm (simplifyHvl hvl), toRef c ]
          )
    ]

  return (rewrt ++ proof)
