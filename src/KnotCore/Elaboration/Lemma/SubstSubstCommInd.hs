
module KnotCore.Elaboration.Lemma.SubstSubstCommInd where

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
    [ sortDeclGroup ntna sdg
    | sdg@(SortGroupDecl _ _ ntns _) <- sdgs,
      ntna <- ntns
    ]

sortDeclGroup :: Elab m =>
  NamespaceTypeName -> SortGroupDecl ->
  m [Coq.Sentence]
sortDeclGroup ntna =
  mutualInduction
    (idGroupLemmaSubstSubstCommInd ntna ntna)
    (lemmaIdentifier ntna)
    (sortDeclAssertionInd ntna)
    (ctorDecl ntna)

lemmaIdentifier ::
  Elab m =>
  NamespaceTypeName ->
  SortTypeName ->
  m (Maybe Coq.Identifier)
lemmaIdentifier ntna stn =
  do
    deps <- getSortNamespaceDependencies stn
    if ntna `elem` deps
       then Just <$> idLemmaSubstSubstCommInd ntna ntna stn
       else return Nothing

sortDeclAssertionInd :: Elab m =>
                        NamespaceTypeName ->
                        SortDecl ->
                        m Coq.Term
sortDeclAssertionInd ntna (SortDecl stn _ _) = localNames $ do

  (stna,_) <- getNamespaceCtor ntna

  xa           <- freshTraceVar ntna
  ta1          <- freshSubtreeVar stna
  ta2          <- freshSubtreeVar stna
  k            <- freshHVarlistVar
  t            <- freshSubtreeVar stn

  let left   = SSubst (TWeaken (TVar xa) (HVVar k)) (SVar ta2)
                 (SSubst (TWeaken (T0 ntna) (HVVar k)) (SVar ta1) (SVar t))
      right  = SSubst (TWeaken (T0 ntna) (HVVar k))
                 (SSubst (TVar xa) (SVar ta2) (SVar ta1))
                 (SSubst (TWeaken (TS ntna (TVar xa)) (HVVar k)) (SVar ta2) (SVar t))

  Coq.TermForall
    <$> sequence [toBinder t, toBinder k, toBinder xa, toBinder ta1, toBinder ta2]
    <*> (Coq.eq <$> toTerm left <*> toTerm right)

ctorDecl :: Elab m => NamespaceTypeName -> ProofCtor m
ctorDecl ntna (CtorVar _ mv) = do

  (stna,_) <- getNamespaceCtor ntna

  xa           <- freshTraceVar ntna
  ta1          <- freshSubtreeVar stna
  ta2          <- freshSubtreeVar stna
  k            <- freshHVarlistVar
  y            <- freshIndexVar (typeNameOf mv)

  init <- sequence
          [ Coq.PrIntros <$> sequence [toId y, toId k, toId xa, toId ta1, toId ta2]
          ]
  finish <- if ntna == typeNameOf mv
            then sequence
                 [ Coq.PrApply
                   <$> (idLemmaSubstSubstIndexCommRightInd ntna ntna >>= toRef)
                ]
            else pure
                 [ Coq.PrTactic "reflexivity" []
                 ]
  let proof = init ++ finish
  return (proof, fieldDecl ntna k xa ta1 ta2)
ctorDecl ntna (CtorTerm cn fds) = localNames $ do

  (stna,_) <- getNamespaceCtor ntna

  xa           <- freshTraceVar ntna
  ta1          <- freshSubtreeVar stna
  ta2          <- freshSubtreeVar stna
  k            <- freshHVarlistVar

  proof <- sequence
    [ Coq.PrSeq <$> sequence
      [ Coq.PrIntros <$> sequence [toId k, toId xa, toId ta1, toId ta2],
        pure Coq.PrSimpl,
        Coq.PrFEqual (length [ () | FieldSubtree{} <- fds ]) <$> toRef cn
      ]
    ]

  return (proof, fieldDecl ntna k xa ta1 ta2)

fieldDecl :: Elab m => NamespaceTypeName ->
   HVarlistVar -> TraceVar -> SubtreeVar -> SubtreeVar -> ProofSubtree m
fieldDecl ntna k xa ta1 ta2 _ bs ih = do

  let fns  = nub [ fn | VleCall _ fn _ <- bs ]
  let hvl  = simplifyHvl $ HVAppend (HVVar k) (evalBindSpec bs)
  weakenCutoffAppend <- idLemmaWeakenCutoffAppend ntna
  weakenTraceAppend  <- idLemmaWeakenTraceAppend


  rewrt <- sequence
    [ Coq.PrRepeat . Coq.PrRewrite <$> (idLemmaStabilitySubst ntna fn >>= toRef)
    | fn <- fns
    ]

  proof <- sequence
    [ Coq.PrRepeat . Coq.PrRewrite <$> toRef weakenCutoffAppend,
      Coq.PrRepeat . Coq.PrRewrite <$> toRef weakenTraceAppend,
      Coq.PrExact
      <$> (Coq.TermApp
           <$> hypothesisRef ih
           <*> sequence [ toTerm hvl, toRef xa, toRef ta1, toRef ta2 ]
          )
    ]

  return (rewrt ++ proof)
