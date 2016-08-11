{-# LANGUAGE GADTs #-}

module KnotCore.Elaboration.Lemma.ShiftSize (lemmas) where

import Coq.StdLib as Coq
import Coq.Syntax as Coq

import KnotCore.Syntax
import KnotCore.Elaboration.Core

import Data.Maybe

lemmas :: Elab m => [SortGroupDecl] -> m [Sentence]
lemmas sdgs =
  sequenceA
    [ sortDeclGroup ntn sdg
    | sdg@(SortGroupDecl _ _ ntns _) <- sdgs,
      ntn <- ntns
    ]

sortDeclGroup :: Elab m => NamespaceTypeName -> SortGroupDecl -> m Sentence
sortDeclGroup ntn sdg =
  SentenceFixpoint . Fixpoint <$> traverse (sortDecl ntn) (sgSorts sdg)

sortDecl :: Elab m => NamespaceTypeName -> SortDecl -> m FixpointBody
sortDecl ntn sd = localNames $ do
  let stn = typeNameOf sd

  cv         <- freshCutoffVar ntn
  sv         <- freshSortVariable stn
  size       <- idFunctionSize stn

  goal <-
    Coq.eq
    <$> (TermApp
         <$> toRef size
         <*> sequenceA [ toTerm (SShift (CVar cv) (SVar sv)) ]
        )
    <*> (TermApp
         <$> toRef size
         <*> sequenceA [ toTerm (SVar sv) ]
        )

  proof <-
    TermMatch
    <$> (MatchItem <$> toRef sv <*> pure Nothing <*> pure Nothing)
    <*> pure (Just goal)
    <*> traverse (ctorDecl cv) (sdCtors sd)

  FixpointBody
    <$> idLemmaShiftSize ntn stn
    <*> sequenceA [toBinder sv, toBinder cv]
    <*> (Just . Struct <$> toId sv)
    <*> pure goal
    <*> pure proof

ctorDecl :: Elab m => CutoffVar -> CtorDecl -> m Equation
ctorDecl _cv (CtorVar cn _mv _wfhyp) = do
  cn' <- toQualId cn
  pure (Equation (PatCtorEx cn' [PatUnderscore]) eqRefl)
ctorDecl cv cd@(CtorReg _cn fds) = localNames $ do
  proofs <- traverse (fieldDecl cv) fds
  Equation
    <$> ctorDecl2Pattern cd
    <*> pure (foldr1 (eqFEqual2 (termIdent "plus")) (eqRefl:catMaybes proofs))

fieldDecl :: Elab m => CutoffVar -> FieldDecl w -> m (Maybe Term)
fieldDecl cv (FieldDeclSort bs sv _svWf) = fmap Just $ do
  let ntn = typeNameOf cv
      stn = typeNameOf sv
  deps <- getSortNamespaceDependencies stn
  if ntn `elem` deps
    then TermApp
         <$> (idLemmaShiftSize ntn stn >>= toRef)
         <*> sequenceA
             [ toRef sv
             , toTerm (CWeaken (CVar cv) (evalBindSpec HV0 bs))
             ]
    else pure eqRefl
fieldDecl _cv (FieldDeclBinding _bs _bv) = pure Nothing
fieldDecl _cv (FieldDeclReference _fv _fvWf) = pure (Just eqRefl)
