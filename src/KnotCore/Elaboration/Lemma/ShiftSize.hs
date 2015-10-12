
module KnotCore.Elaboration.Lemma.ShiftSize where

import Control.Applicative
import Data.Maybe

import qualified Coq.StdLib as Coq
import qualified Coq.Syntax as Coq

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
    (idGroupLemmaShiftSize ntn)
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
       then Just <$> idLemmaShiftSize ntn stn
       else return Nothing

sortDeclAssertionInd :: Elab m =>
                        NamespaceTypeName ->
                        SortDecl ->
                        m Coq.Term
sortDeclAssertionInd ntn (SortDecl stn _ _) = localNames $ do

  c          <- freshCutoffVar ntn
  t          <- freshSubtreeVar stn
  size       <- idFunctionSize stn

  left       <- Coq.TermApp
                  <$> toRef size
                  <*> sequence [ toTerm (SShift (CVar c) (SVar t)) ]
  right      <- Coq.TermApp
                  <$> toRef size
                  <*> sequence [ toTerm (SVar t) ]

  Coq.TermForall
    <$> sequence [toBinder t, toBinder c]
    <*> (Coq.eq <$> pure left <*> pure right)

ctorDecl :: Elab m => NamespaceTypeName -> ProofCtor m
ctorDecl ntn (CtorVar _ _) = do

  x       <- freshIndexVar ntn
  c       <- freshCutoffVar ntn

  proof   <- sequence
               [ Coq.PrIntros <$> sequence [toId x, toId c],
                 pure Coq.PrReflexivity
               ]
  return (proof, fieldDecl c)
ctorDecl ntn (CtorTerm _ fds) = localNames $ do

  c       <- freshCutoffVar ntn

  proof <- sequence
    [ Coq.PrSeq <$> sequence
      [ Coq.PrIntros <$> sequence [toId c],
        pure $ Coq.PrSimpl,
        pure $ Coq.PrFEqual 1 (Coq.termIdent "S"),
        -- Bindings are erased so we need to count only the
        -- subtree bindings that contribute to the size.
        if null [ () | FieldSubtree{} <- fds ]
          then pure $ Coq.PrReflexivity
          else pure $ Coq.PrRepeat $ Coq.PrFEqual 2 (Coq.termIdent "plus")
      ]
    ]

  return (proof, fieldDecl c)

fieldDecl :: Elab m => CutoffVar -> ProofSubtree m
fieldDecl c _ bs ih = do

  let c' = simplifyCutoff $ CWeaken (CVar c) (evalBindSpec bs)

  proof <- sequence
    [ Coq.PrExact
      <$> (Coq.TermApp
           <$> hypothesisRef ih
           <*> sequence [ toTerm c' ]
          )
    ]

  return proof
