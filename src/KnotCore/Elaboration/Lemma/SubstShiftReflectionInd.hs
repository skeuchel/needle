
module KnotCore.Elaboration.Lemma.SubstShiftReflectionInd where

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
    [ sortDeclGroup ntn sdg
    | sdg@(SortGroupDecl _ _ ntns _) <- sdgs,
      ntn <- ntns
    ]

sortDeclGroup :: Elab m =>
  NamespaceTypeName -> SortGroupDecl ->
  m [Coq.Sentence]
sortDeclGroup ntn =
  mutualInduction
    (idGroupLemmaSubstShiftReflectionInd ntn)
    (lemmaIdentifier ntn)
    (sortDeclAssertionInd ntn)
    (ctorDecl ntn)

lemmaIdentifier ::
  Elab m =>
  NamespaceTypeName ->
  SortTypeName ->
  m (Maybe Coq.Identifier)
lemmaIdentifier ntn stn =
  do
    deps <- getSortNamespaceDependencies stn
    if ntn `elem` deps
       then Just <$> idLemmaSubstShiftReflectionInd ntn stn
       else return Nothing

sortDeclAssertionInd :: Elab m =>
                        NamespaceTypeName ->
                        SortDecl ->
                        m Coq.Term
sortDeclAssertionInd ntn (SortDecl congStn _ _) = localNames $ do

  (subStn,_) <- getNamespaceCtor ntn

  k          <- freshHVarlistVar
  s          <- freshSubtreeVar subStn
  t          <- freshSubtreeVar congStn

  let left    = SSubst (TWeaken (T0 ntn) (HVVar k)) (SVar s)
                  (SShift (CWeaken (C0 ntn) (HVVar k)) (SVar t))
      right   = SVar t

  Coq.TermForall
    <$> sequence [toBinder t, toBinder k, toBinder s]
    <*> (Coq.eq <$> toTerm left <*> toTerm right)

ctorDecl :: Elab m => NamespaceTypeName -> ProofCtor m
ctorDecl ntn (CtorVar _ mv) = do

  (stn,_) <- getNamespaceCtor ntn

  x       <- freshIndexVar ntn
  k       <- freshHVarlistVar
  s       <- freshSubtreeVar stn

  init <- sequence
          [ Coq.PrIntros <$> sequence [toId x, toId k, toId s]
          ]
  finish <- if ntn == typeNameOf mv
              then sequence
                   [ Coq.PrApply
                     <$> (idLemmaSubstIndexShiftIndexReflectionInd ntn >>= toRef)
                   ]
              else pure
                   [ Coq.PrTactic "reflexivity" []
                   ]
  let proof = init ++ finish
  return (proof, fieldDecl ntn k s)
ctorDecl ntn (CtorTerm cn fds) = localNames $ do

  (stn,_) <- getNamespaceCtor ntn

  k     <- freshHVarlistVar
  s     <- freshSubtreeVar stn

  proof <- sequence
    [ Coq.PrSeq <$> sequence
      [ Coq.PrIntros <$> sequence [toId k, toId s],
        pure Coq.PrSimpl,
        Coq.PrFEqual (length [ () | FieldSubtree{} <- fds ]) <$> toRef cn
      ]
    ]

  return (proof, fieldDecl ntn k s)

fieldDecl :: Elab m => NamespaceTypeName ->
                       HVarlistVar  -> SubtreeVar -> ProofSubtree m
fieldDecl ntn k s _ bs ih = do

  let fns  = nub [ fn | VleCall _ fn _ <- bs ]
  let hvl  = simplifyHvl $ HVAppend (HVVar k) (evalBindSpec bs)
  weakenCutoffAppend <- idLemmaWeakenCutoffAppend ntn
  weakenTraceAppend  <- idLemmaWeakenTraceAppend


  rewrt <- sequence
    [ Coq.PrRepeat . Coq.PrRewrite <$> (idLemmaStabilityShift ntn fn >>= toRef)
    | fn <- fns
    ]

  proof <- sequence
    [ Coq.PrRepeat . Coq.PrRewrite <$> toRef weakenCutoffAppend,
      Coq.PrRepeat . Coq.PrRewrite <$> toRef weakenTraceAppend,
      Coq.PrExact
      <$> (Coq.TermApp
           <$> hypothesisRef ih
           <*> sequence [ toTerm hvl, toRef s ]
          )
    ]

  return (rewrt ++ proof)
