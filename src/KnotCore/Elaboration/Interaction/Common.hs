{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -Wall #-}

module KnotCore.Elaboration.Interaction.Common where

import Coq.StdLib as Coq
import Coq.Syntax as Coq

import KnotCore.Syntax
import KnotCore.Elaboration.Core

import Data.Maybe

termInduction :: forall m. Elab m =>
  (SortTypeName -> m Identifier) -> [Binder] ->
  (SortVariable -> m Term) ->
  (CtorName -> IndexVar -> m Term) ->
  (BindSpec -> SortVariable ->  m Term) ->
  [SortDecl] -> m Sentence
termInduction mkLem binders mkGoal proofVar proofField sds =
    SentenceFixpoint . Fixpoint <$> localNames (traverse sortDecl sds)
  where
    sortDecl :: SortDecl -> m FixpointBody
    sortDecl sd = do
      let stn = typeNameOf sd
      sv      <- freshSortVariable stn
      goal    <- mkGoal sv
      cds     <- freshen' (sdCtors sd)
      proof <-
        TermMatch
        <$> (MatchItem <$> toRef sv <*> pure Nothing <*> pure Nothing)
        <*> pure (Just goal)
        <*> traverse ctorDecl cds

      FixpointBody
        <$> mkLem stn
        <*> ((:) <$> toBinder sv <*> pure binders)
        <*> (Just . Struct <$> toId sv)
        <*> pure goal
        <*> pure proof

    ctorDecl :: CtorDecl -> m Equation
    ctorDecl (CtorVar cn mv _wfhyp) = do
      x     <- toIndex mv
      Equation
        <$> (PatCtor <$> toQualId cn <*> sequenceA [toId x])
        <*> proofVar cn x
    ctorDecl cd@(CtorReg cn fds) = localNames $ do
      proofs <- sequenceA $ mapMaybe fieldDecl fds
      Equation
        <$> ctorDecl2Pattern cd
        <*> (eqFEqualn <$> toRef cn <*> pure proofs)

    fieldDecl :: FieldDecl w -> Maybe (m Term)
    fieldDecl (FieldDeclSort bs sv _svWf)    = Just (proofField bs sv)
    fieldDecl (FieldDeclBinding _bs _bv)     = Nothing
    fieldDecl (FieldDeclReference _fv _fvWf) = error "NOT IMPLEMENTED"
