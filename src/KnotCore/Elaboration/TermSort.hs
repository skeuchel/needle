
module KnotCore.Elaboration.TermSort where

import Control.Applicative
import Data.List
import Data.Maybe

import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core

eSortGroupDecls :: Elab m => [SortGroupDecl] -> m [Sentence]
eSortGroupDecls sgds = intercalate [SentenceBlankline] <$> traverse eSortGroupDecl sgds

eSortGroupDecl :: Elab m => SortGroupDecl -> m [Sentence]
eSortGroupDecl sgd = do
  terms   <- eTermSortGroupDecl sgd
  schemes <- eSchemeSortGroupDecl sgd

  return $ terms : schemes

eTermSortGroupDecl :: Elab m => SortGroupDecl -> m Sentence
eTermSortGroupDecl sg =
  fmap SentenceInductive $
    Inductive <$> traverse eTermSortDecl (sgSorts sg)

eTermSortDecl :: Elab m => SortDecl -> m InductiveBody
eTermSortDecl (SortDecl stn _ ctors) =
  InductiveBody
    <$> toId stn
    <*> pure []
    <*> pure (TermSort Set)
    <*> traverse eTermCtorDecl ctors

eTermCtorDecl :: Elab m => CtorDecl -> m InductiveCtor
eTermCtorDecl (CtorVar cn fv _)      =
  InductiveCtor
    <$> toId cn
    <*> sequenceA [ toIndex fv >>= toBinder ] -- Single Field
    <*> pure Nothing                  -- Normal ADT constructor
eTermCtorDecl (CtorReg cn fields) =
  InductiveCtor
    <$> toId cn
    <*> sequenceA (eFieldDeclBinders fields)
    <*> pure Nothing                  -- Normal ADT constructor

eSchemeSortGroupDecl :: Elab m => SortGroupDecl -> m [Sentence]
eSchemeSortGroupDecl sg = do
  let sgtn = typeNameOf sg
      sds  = sgSorts sg

  individual <- SentenceScheme . Scheme
                  <$> traverse eSchemeSortDecl sds
  group      <- SentenceCombinedScheme
                  <$> idInductionSortGroup sgtn
                  <*> traverse (idInductionSort . typeNameOf) sds
  case sds of
    [_] -> return [individual]
    _   -> return [individual,group]

eSchemeSortDecl :: Elab m => SortDecl -> m SchemeBody
eSchemeSortDecl (SortDecl stn _ _) =
  SchemeInduction
    <$> idInductionSort stn
    <*> toId stn
