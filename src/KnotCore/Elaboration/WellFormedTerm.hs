{-# LANGUAGE GADTs #-}

module KnotCore.Elaboration.WellFormedTerm where

import Control.Applicative
import Control.Monad
import Data.Maybe

import Coq.StdLib
import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core
import KnotCore.Elaboration.Eq

eSortGroupDecls :: Elab m => [SortGroupDecl] -> m [Sentence]
eSortGroupDecls = traverse eSortGroupDecl

eSortGroupDecl ::  Elab m => SortGroupDecl -> m Sentence
eSortGroupDecl sg =
  fmap SentenceInductive $
    Inductive <$> traverse eSortDecl (sgSorts sg)

eSortDecl :: Elab m => SortDecl -> m InductiveBody
eSortDecl (SortDecl stn _ ctors) = localNames $ do
  h  <- freshHVarlistVar

  InductiveBody
    <$> idRelationWellFormed stn
    <*> sequenceA [toBinder h]
    <*> (TermFunction
         <$> toRef stn
         <*> pure (TermSort Prop)
        )
    <*> (freshen ctors >>= traverse (eCtorDecl h))

eCtorDecl :: Elab m => HVarlistVar -> CtorDecl -> m InductiveCtor
eCtorDecl h (CtorVar cn mv _) = localNames $ do
  stn <- lookupCtorType cn
  -- TOneverDO: used cached name
  i   <- toIndex mv
  wfi <- freshVariable "wfi" =<< toTerm (WfIndex (HVVar h) (IVar i))

  InductiveCtor
    <$> idRelationWellFormedCtor cn
    <*> sequenceA [toBinder i, toBinder wfi]
    <*> (Just <$> toTerm (WfSort (HVVar h) (SCtorVar stn cn (IVar i))))

eCtorDecl h (CtorReg cn fields) = localNames $ do
  stn <- lookupCtorType cn
  (binderss,fs) <- unzip . catMaybes <$> traverse (eFieldDecl (HVVar h)) fields

  InductiveCtor
    <$> idRelationWellFormedCtor cn
    <*> pure (concat binderss)
    <*> (Just <$> toTerm (WfSort (HVVar h) (SCtorReg stn cn fs)))

eFieldDecl :: Elab m => HVarlist -> FieldDecl w -> m (Maybe (Binders,Field w))
eFieldDecl h (FieldDeclSort bs sv _svWf) = do
  -- TOneverDO: reuse svWf
  let wfsv = WfSort (HVAppend h (evalBindSpec HV0 bs)) (SVar sv)
  svWf <- toTerm wfsv >>= freshVariable "wf"
  Just
    <$> ((,)
           <$> sequenceA
                [ toImplicitBinder sv
                , toBinder svWf
                ]
           <*> pure (FieldSort (SVar sv))
        )
eFieldDecl _ (FieldDeclBinding _bs _bv)  = pure Nothing
eFieldDecl _ (FieldDeclReference{})      =
  error "KnotCore.Elaboration.WellFormedTerm.eFieldDecl: not implemented"
