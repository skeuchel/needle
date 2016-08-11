{-# LANGUAGE GADTs #-}

module KnotCore.Elaboration.Lemma.WellFormedInversion where

import Coq.Syntax
import Coq.StdLib

import KnotCore.Syntax
import KnotCore.Elaboration.Core

import Control.Applicative
import Control.Monad
import Data.List (intersect, nub)
import Data.Maybe (catMaybes, mapMaybe)
import Data.Traversable (for, traverse)

lemmas :: Elab m => [SortGroupDecl] -> m [Sentence]
lemmas sdgs = concat <$>
  sequenceA
    [ sortDecl sd
    | sdg <- sdgs, sd <- sgSorts sdg
    ]

sortDecl :: Elab m => SortDecl -> m [Sentence]
sortDecl (SortDecl _ _ cds) =
  concat <$> traverse conDecl cds

ctorDecl2SymbolicTerm :: CtorDecl -> SymbolicTerm
ctorDecl2SymbolicTerm (CtorVar cn rv _) =
  SymCtorVarFree Nil cn rv
ctorDecl2SymbolicTerm (CtorReg cn fds) =
  SymCtorReg Nil cn
    [ case fd of
        FieldDeclSort bs sv _svWf   -> SymFieldSort Nil bs (SymSubtree bs sv)   -- TODO
        FieldDeclBinding _bs bv     -> SymFieldBinding Nil bv                   -- TODO
        FieldDeclReference fv _fvWf -> SymFieldReferenceFree Nil fv             -- TODO
    | fd <- fds
    ]

ctorDecl2WfPattern :: Elab m => HVarlistVar -> CtorDecl -> m Pattern
ctorDecl2WfPattern _ (CtorVar cn rv wf) = do
  iv <- toIndex rv
  PatCtorEx
    <$> (idRelationWellFormedCtor cn >>= toQualId)
    <*> (sequenceA . concat $
         [ [] -- [pure PatUnderscore]
         , map (fmap PatQualId)
             [toQualId iv, toQualId wf]
         ])

ctorDecl2WfPattern _ (CtorReg cn fds) =
  PatCtorEx
    <$> (idRelationWellFormedCtor cn >>= toQualId)
    <*> (sequenceA . concat $
         [ [] -- [pure PatUnderscore]
         , map (fmap PatQualId) . concat .  catMaybes $
           [ case fd of
               FieldDeclSort _bs sv svWf  -> Just [toQualId sv, toQualId svWf]
               FieldDeclBinding _bs _bv   -> Nothing
               FieldDeclReference fv fvWf -> Just [toIndex fv >>= toQualId, toQualId fvWf]
           | fd <- fds
           ]
         ])

conDecl :: Elab m => CtorDecl -> m [Sentence]
conDecl cd = do
  k   <- freshHVarlistVar
  st  <- symbolicTermToSTerm $ ctorDecl2SymbolicTerm cd
  wfSt <- WellFormedSortHyp
            <$> freshHypothesis
            <*> pure (WfSort (HVVar k) st)
  let stn  = typeNameOf st
  -- The meta-variable representing the symbolic term in the match.
  stv <- freshSortVariable stn

  case cd of
    CtorReg cn fds -> do
      binders <-
        sequenceA . concat $
          [ [toBinder k]
          , eFieldDeclBinders fds
          , [toBinder wfSt]
          ]
      sequenceA . catMaybes $
        [ case fd of
            FieldDeclSort bs sv svWf -> Just $ do
              prop <- toTerm $
                WfSort
                  (HVAppend (HVVar k) (evalBindSpec HV0 bs))
                  (SVar sv)
              innerMatch <-
                TermMatch
                  <$> (MatchItem
                       <$> toRef stv
                       <*> pure Nothing
                       <*> pure Nothing
                      )
                  <*> pure (Just (TermSort Prop))
                  <*> sequenceA
                      [ Equation
                        <$> ctorDecl2Pattern cd
                        <*> pure prop
                      , Equation
                        <$> pure PatUnderscore
                        <*> pure true
                      ]
              body <-
                TermMatch
                <$> (MatchItem
                     <$> toRef wfSt
                     <*> pure Nothing
                     <*> (Just <$> toMatchItem (WfSort (HVVar k) (SVar stv)))
                    )
                <*> pure (Just innerMatch)
                <*> sequenceA
                    [ Equation
                      <$> ctorDecl2WfPattern k cd
                      <*> toRef svWf
                    , Equation
                      <$> pure PatUnderscore
                      <*> pure (termIdent "I")
                    ]
              def <-
                Definition
                  <$> idLemmaWellFormedInversion stn cn i
                  <*> pure binders
                  <*> pure (Just prop)
                  <*> pure body

              return (SentenceDefinition def)
            FieldDeclBinding _bs _bv -> Nothing
            FieldDeclReference _fv _fvWf ->
              error $
                "KnotCore.Elaboration.Lemma.WellFormedInversion." ++
                "FieldReference: not implemented"
        | (i,fd) <- zip [0..] fds
        ]

    CtorVar cn rv wf -> do
      -- TODO: combine with the above
      iv <- toIndex rv
      binders <- sequenceA
        [ toBinder k
        , toBinder iv
        , toBinder wfSt
        ]
      prop <- toTerm (WfIndex (HVVar k) (IVar iv))
      innerMatch <-
        TermMatch
          <$> (MatchItem
               <$> toRef stv
               <*> pure Nothing
               <*> pure Nothing
              )
          <*> pure (Just (TermSort Prop))
          <*> sequenceA
              [ Equation
                <$> ctorDecl2Pattern cd
                <*> pure prop
              , Equation
                <$> pure PatUnderscore
                <*> pure true
              ]
      body <-
        TermMatch
        <$> (MatchItem
             <$> toRef wfSt
             <*> pure Nothing
             <*> (Just <$> toMatchItem (WfSort (HVVar k) (SVar stv)))
            )
        <*> pure (Just innerMatch)
        <*> sequenceA
            [ Equation
              <$> ctorDecl2WfPattern k cd
              <*> toRef wf
            , Equation
              <$> pure PatUnderscore
              <*> pure (termIdent "I")
            ]
      def <-
        Definition
          <$> idLemmaWellFormedInversion stn cn 1
          <*> pure binders
          <*> pure (Just prop)
          <*> pure body

      return [SentenceDefinition def]
