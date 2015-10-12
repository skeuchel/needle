
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
eSortGroupDecls = mapM eSortGroupDecl

eSortGroupDecl ::  Elab m => SortGroupDecl -> m Sentence
eSortGroupDecl sg =
  fmap SentenceInductive $
    Inductive <$> mapM eSortDecl (sgSorts sg)

eSortDecl :: Elab m => SortDecl -> m InductiveBody
eSortDecl (SortDecl stn _ ctors) = localNames $ do
  h  <- freshHVarlistVar

  InductiveBody
    <$> idRelationWellFormed stn
    <*> sequence [toBinder h]
    <*> (TermFunction
         <$> toRef stn
         <*> pure (TermSort Prop)
        )
    <*> (freshen ctors >>= mapM (eCtorDecl h))

eCtorDecl :: Elab m => HVarlistVar -> CtorDecl -> m InductiveCtor
eCtorDecl h (CtorVar cn mv) = localNames $ do
  i   <- toIndex mv
  wfi <- freshVariable "wfi" =<< toTerm (WfIndex (HVVar h) (IVar i))

  InductiveCtor
    <$> idRelationWellFormedCtor cn
    <*> sequence [toImplicitBinder i, toBinder wfi]
    <*> (Just <$> toTerm (WfTerm (HVVar h) (SCtorVar cn (IVar i))))

eCtorDecl h (CtorTerm cn fields) = localNames $ do
  let fds = mapMaybe (eFieldDecl (HVVar h)) fields
      svs = map fst fds

  binders <- forM fds $ \(sv,wfsv) ->
               sequence
               [ toImplicitBinder sv
               , toTerm wfsv >>= freshVariable "wf" >>= toBinder
               ]

  InductiveCtor
    <$> idRelationWellFormedCtor cn
    <*> pure (concat binders)
    <*> (Just <$> toTerm (WfTerm (HVVar h) (SCtorTerm cn (map SVar svs))))

eFieldDecl :: HVarlist -> FieldDecl -> Maybe (SubtreeVar,WellFormedTerm)
eFieldDecl h (FieldSubtree t bs) = Just (t, WfTerm (simplifyHvl $ HVAppend h (evalBindSpec bs)) (SVar t))
eFieldDecl _ (FieldBinding _)    = Nothing
