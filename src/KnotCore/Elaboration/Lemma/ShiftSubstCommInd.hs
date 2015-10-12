
module KnotCore.Elaboration.Lemma.ShiftSubstCommInd where

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
    (idGroupLemmaShiftSubstCommInd ntna ntnb)
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
       then Just <$> idLemmaShiftSubstCommInd ntna ntnb stn
       else return Nothing

sortDeclAssertionInd :: Elab m =>
                        NamespaceTypeName ->
                        NamespaceTypeName ->
                        SortDecl ->
                        m Coq.Term
sortDeclAssertionInd ntna ntnb (SortDecl stn _ _) = localNames $ do
  (stnb,_) <- getNamespaceCtor ntnb
  depsb    <- getSortNamespaceDependencies stnb

  ca      <- freshCutoffVar ntna
  tb      <- freshSubtreeVar stnb
  t       <- freshSubtreeVar stn
  h       <- freshHVarlistVar

  let left   = SShift (CWeaken (CVar ca) (HVVar h))
                   (SSubst (TWeaken (T0 ntnb) (HVVar h)) (SVar tb) (SVar t))
      -- α ≡ β
      right1 = SSubst (TWeaken (T0 ntnb) (HVVar h))
                 (SShift (CVar ca) (SVar tb))
                 (SShift (CWeaken (CS (CVar ca)) (HVVar h)) (SVar t))
      -- α ≢ β, α ∈ β
      right2 = SSubst (TWeaken (T0 ntnb) (HVVar h))
                 (SShift (CVar ca) (SVar tb))
                 (SShift (CWeaken (CVar ca) (HVVar h)) (SVar t))
      -- α ≢ β, α ∉ β.
      right3 = SSubst (TWeaken (T0 ntnb) (HVVar h))
                 (SVar tb)
                 (SShift (CWeaken (CVar ca) (HVVar h)) (SVar t))
      right | ntna == ntnb      = right1
            | ntna `elem` depsb = right2
            | otherwise         = right3

  Coq.TermForall
    <$> sequence [toBinder t, toBinder h, toBinder ca, toBinder tb]
    <*> (Coq.eq <$> toTerm left <*> toTerm right)

ctorDecl :: Elab m => NamespaceTypeName -> NamespaceTypeName -> ProofCtor m
ctorDecl ntna ntnb (CtorVar _ mv) = do

  (stnb,_) <- getNamespaceCtor ntnb
  depsb    <- getSortNamespaceDependencies stnb
  ca       <- freshCutoffVar ntna
  tb       <- freshSubtreeVar stnb
  k        <- freshHVarlistVar
  x        <- freshIndexVar (typeNameOf mv)

  init <- sequence
          [ Coq.PrIntros <$> sequence [toId x, toId k, toId ca, toId tb]
          ]
  finish <- if ntnb == typeNameOf mv && (ntna `elem` depsb)
              then sequence
                   [ Coq.PrApply
                     <$> (idLemmaShiftSubstIndexCommInd ntna ntnb >>= toRef)
                   ]
              else pure
                   [ Coq.PrTactic "reflexivity" []
                   ]
  let proof = init ++ finish
  return (proof, fieldDecl ntna ntnb k ca tb)
ctorDecl ntna ntnb (CtorTerm cn fds) = localNames $ do

  (stnb,_) <- getNamespaceCtor ntnb
  ca       <- freshCutoffVar ntna
  tb       <- freshSubtreeVar stnb
  k        <- freshHVarlistVar

  proof <-
    sequence
      [ Coq.PrSeq <$> sequence
        [ Coq.PrIntros <$> sequence [toId k, toId ca, toId tb],
          pure Coq.PrSimpl,
          Coq.PrFEqual (length [ () | FieldSubtree{} <- fds ]) <$> toRef cn
        ]
      ]

  return (proof, fieldDecl ntna ntnb k ca tb)

fieldDecl :: Elab m => NamespaceTypeName -> NamespaceTypeName ->
                       HVarlistVar  -> CutoffVar -> SubtreeVar -> ProofSubtree m
fieldDecl ntna ntnb k ca tb _ bs ih = do

  let fns  = nub [ fn | VleCall _ fn _ <- bs ]
      ntns = nub [ ntna, ntnb ]
  let h  = simplifyHvl $ HVAppend (HVVar k) (evalBindSpec bs)
  weakenCutoffAppend <- idLemmaWeakenCutoffAppend ntna
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
           <*> sequence [ toTerm h, toRef ca, toRef tb ]
          )
    ]

  return (rewrt ++ proof)
