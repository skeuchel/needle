
module KnotCore.Elaboration.Lemma.SubstShiftCommInd where

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
    [ sortDeclGroup ntna ntnb sdg
    | sdg@(SortGroupDecl _ _ ntns _) <- sdgs,
      ntna <- ntns,
      ntnb <- ntns
    ]

sortDeclGroup :: Elab m =>
  NamespaceTypeName -> NamespaceTypeName -> SortGroupDecl ->
  m [Coq.Sentence]
sortDeclGroup ntna ntnb =
  mutualInduction
    (idGroupLemmaSubstShiftCommInd ntna ntnb)
    (lemmaIdentifier ntna ntnb)
    (sortDeclAssertionInd ntna ntnb)
    (ctorDecl ntna ntnb)

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
                        SortDecl ->
                        m Coq.Term
sortDeclAssertionInd ntna ntnb (SortDecl stn _ _) = localNames $ do
  (stna,_) <- getNamespaceCtor ntna
  depsa    <- getSortNamespaceDependencies stna

  xa      <- freshTraceVar ntna
  ta      <- freshSubtreeVar stna
  h       <- freshHVarlistVar
  t       <- freshSubtreeVar stn

  let -- α ≡ β \/ α ≢ β, β ∈ α:
      left1  = SSubst (TWeaken (TS ntnb (TVar xa)) (HVVar h)) (SVar ta)
                 (SShift (CWeaken (C0 ntnb) (HVVar h)) (SVar t))
      -- α ≢ β, β ∉ α:
      left2  = SSubst (TWeaken (TVar xa) (HVVar h)) (SVar ta)
                 (SShift (CWeaken (C0 ntnb) (HVVar h)) (SVar t))
      left  | ntna == ntnb      = left1
            | ntnb `elem` depsa = left1
            | otherwise         = left2
      right  = SShift (CWeaken (C0 ntnb) (HVVar h))
                 (SSubst (TWeaken (TVar xa) (HVVar h)) (SVar ta) (SVar t))

  Coq.TermForall
    <$> sequence [toBinder t, toBinder h, toBinder xa, toBinder ta]
    <*> (Coq.eq <$> toTerm left <*> toTerm right)

ctorDecl :: Elab m => NamespaceTypeName -> NamespaceTypeName -> ProofCtor m
ctorDecl ntna ntnb (CtorVar _ mv) = do

  (stna,_) <- getNamespaceCtor ntna
  depsa    <- getSortNamespaceDependencies stna

  xa      <- freshTraceVar ntnb
  ta      <- freshSubtreeVar stna
  h       <- freshHVarlistVar
  y        <- freshIndexVar (typeNameOf mv)

  init <- sequence
          [ Coq.PrIntros <$> sequence [toId y, toId h, toId xa, toId ta]
          ]
  finish <- if ntna == typeNameOf mv && (ntnb `elem` depsa)
              then sequence
                   [ Coq.PrApply
                     <$> (idLemmaSubstShiftIndexCommInd ntna ntnb >>= toRef)
                   ]
              else pure
                   [ Coq.PrTactic "reflexivity" []
                   ]
  let proof = init ++ finish
  return (proof, fieldDecl ntna ntnb h xa ta)
ctorDecl ntna ntnb (CtorTerm cn fds) = do

  (stna,_) <- getNamespaceCtor ntna
  xa      <- freshTraceVar ntnb
  ta      <- freshSubtreeVar stna
  h       <- freshHVarlistVar

  proof <-
    sequence
      [ Coq.PrSeq <$> sequence
        [ Coq.PrIntros <$> sequence [toId h, toId xa, toId ta],
          pure Coq.PrSimpl,
          Coq.PrFEqual (length [ () | FieldSubtree{} <- fds ]) <$> toRef cn
        ]
      ]

  return (proof, fieldDecl ntna ntnb h xa ta)

fieldDecl :: Elab m => NamespaceTypeName -> NamespaceTypeName ->
                       HVarlistVar  -> TraceVar -> SubtreeVar -> ProofSubtree m
fieldDecl ntna ntnb k xa ta _ bs ih = do

  let fns  = nub [ fn | VleCall _ fn _ <- bs ]
      ntns = nub [ ntna, ntnb ]
  let h  = simplifyHvl $ HVAppend (HVVar k) (evalBindSpec bs)
  weakenCutoffAppend <- idLemmaWeakenCutoffAppend ntnb
  weakenTraceAppend  <- idLemmaWeakenTraceAppend

  rewrt <- concat <$> sequence
    [ sequence
      [ Coq.PrRepeat . Coq.PrRewrite <$> (idLemmaStabilityShift ntn fn >>= toRef),
        Coq.PrRepeat . Coq.PrRewrite <$> (idLemmaStabilitySubst ntn fn >>= toRef)
      ]

    | fn <- fns, ntn <- ntns
    ]

  proof <- sequence
    [ Coq.PrRepeat . Coq.PrRewrite <$> toRef weakenCutoffAppend,
      Coq.PrRepeat . Coq.PrRewrite <$> toRef weakenTraceAppend,
      Coq.PrExact
      <$> (Coq.TermApp
           <$> hypothesisRef ih
           <*> sequence [ toTerm h, toRef xa, toRef ta ]
          )
    ]

  return (rewrt ++ proof)
