{-# LANGUAGE GADTs #-}

module KnotCore.Elaboration.Lemma.WeakenWfTerm where

import Coq.StdLib
import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core
import KnotCore.Elaboration.Eq

import Control.Applicative
import Control.Monad ((>=>))
import Data.Maybe (catMaybes)
import Data.Traversable (for, traverse, sequenceA)

lemmas :: Elab m => [SortGroupDecl] -> m [Sentence]
lemmas sgds = traverse eSortDecl (concatMap sgSorts sgds)

eSortDecl :: Elab m => SortDecl -> m Sentence
eSortDecl (SortDecl stn _ _) = localNames $ do

  weaken    <- idLemmaWeakenWellFormedSort stn
  k         <- freshHVarlistVar
  ntns      <- getNamespaces

  h         <- freshHVarlistVar
  t         <- freshSortVariable stn
  wft       <- freshVariable "wf" =<< toTerm (WfSort (HVVar h) (SVar t))

  hv0       <- idCtorHVarlistNil
  hvs       <- idCtorHVarlistCons

  goal <-
    TermForall
      <$> sequenceA [toBinder h, toBinder t, toBinder wft]
      <*> toTerm (WfSort (HVAppend (HVVar h) (HVVar k)) (SWeaken (SVar t) (HVVar k)))

  recursiveCall <-
    TermApp
    <$> toRef weaken
    <*> sequenceA [toRef k, toRef h, toRef t, toRef wft]

  eq_h0 <-
    Equation
    <$> (PatCtor
           <$> toQualId hv0
           <*> pure []
        )
    <*> (TermAbs
           <$> sequenceA [toBinder h, toBinder t, toBinder wft]
           <*> toRef wft
        )

  eq_hs <- for ntns $ \ntn ->
    Equation
    <$> (PatCtor <$> toQualId hvs <*> sequenceA [toId ntn, toId k])
    <*> (TermAbs
           <$> sequenceA [toBinder h, toBinder t, toBinder wft]
           <*> (TermApp
                  <$> (idLemmaShiftWellFormedSort ntn stn >>= toRef)
                  <*> sequenceA
                      [ toTerm (HVAppend (HVVar h) (HVVar k))
                      , toTerm (SWeaken (SVar t) (HVVar k))
                      , pure recursiveCall
                      , toTerm (C0 ntn)
                      , toTerm (HVS ntn (HVAppend (HVVar h) (HVVar k)))
                      , TermApp
                          <$> (idRelationHVarlistInsertHere ntn >>= toRef)
                          <*> sequenceA
                              [ toTerm (HVAppend (HVVar h) (HVVar k))
                              ]
                      ]
               )
        )

  body <-
    TermMatch
      <$> (MatchItem <$> toRef k <*> pure Nothing <*> pure Nothing)
      <*> (Just <$> pure goal)
      <*> pure (eq_h0:eq_hs)

  --     | H0 => fun (h : Hvl) (t : Tm) (wft : wfTm h t) => wft
  --     | HS TM k =>
  --       fun (h : Hvl) (t : Tm) (H : wfTm h t) =>
  --         shift_wfTm (appendHvl h k) (weakenTm t k)
  --                    (weaken_wfTm k h t H) C0 (HS TM (appendHvl h k))
  --                    (shifthvl_TM_here (appendHvl h k))



  SentenceFixpoint . Fixpoint <$> sequenceA
    [ FixpointBody
      <$> toId weaken
      <*> sequenceA [toBinder k]
      <*> (Just . Struct <$> toId k)
      <*> pure goal
      <*> pure body
    ]
