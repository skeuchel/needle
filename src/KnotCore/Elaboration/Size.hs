{-# LANGUAGE GADTs #-}

module KnotCore.Elaboration.Size where

import qualified Coq.StdLib as Coq
import qualified Coq.Syntax as Coq

import KnotCore.Syntax
import KnotCore.Elaboration.Core

import Control.Applicative
import Control.Monad
import Data.Maybe

eSortGroupDecls :: Elab m => [SortGroupDecl] -> m [Coq.Sentence]
eSortGroupDecls = traverse eSortGroupDecl

eSortGroupDecl :: Elab m => SortGroupDecl -> m Coq.Sentence
eSortGroupDecl sg =
  Coq.SentenceFixpoint . Coq.Fixpoint
  <$> traverse eSortDecl (sgSorts sg)

eSortDecl :: Elab m => SortDecl -> m Coq.FixpointBody
eSortDecl (SortDecl stn _ ctors) = localNames $
  do
    size       <- idFunctionSize stn
    matchItem  <- freshSortVariable stn
    binders    <- sequenceA [ toBinder matchItem ]
    anno       <- Just . Coq.Struct <$> toId matchItem
    retType    <- pure Coq.nat
    body       <-
      Coq.TermMatch
        <$> (Coq.MatchItem
               <$> toRef matchItem
               <*> pure Nothing
               <*> pure Nothing)
        <*> pure Nothing
        <*> traverse (freshen >=> eCtorDecl) ctors
    return $ Coq.FixpointBody size binders anno retType body

eCtorDecl :: Elab m => CtorDecl -> m Coq.Equation
eCtorDecl (CtorVar cn mv _) =
  do
    index   <- toIndex mv
    pattern <- Coq.PatCtor
                 <$> toQualId cn
                 <*> sequenceA [ toId index ]
    return $ Coq.Equation pattern (Coq.TermNum 1)
eCtorDecl (CtorReg cn fields) =
  do
    pattern <- Coq.PatCtor
                 <$> toQualId cn
                 <*> sequenceA (eFieldDeclIdentifiers fields)
    sizes  <- eFieldDecls fields
    let rhs = foldr1 Coq.plus (Coq.TermNum 1:sizes)
    return $ Coq.Equation pattern rhs

eFieldDecls :: Elab m => [FieldDecl w] -> m Coq.Terms
eFieldDecls = fmap catMaybes . traverse eFieldDecl

eFieldDecl :: Elab m => FieldDecl w -> m (Maybe Coq.Term)
eFieldDecl (FieldDeclBinding _bs _bv) = pure Nothing
eFieldDecl (FieldDeclSort _bs sv _svWf) = fmap Just $
  Coq.TermApp
    <$> (idFunctionSize (typeNameOf sv) >>= toRef)
    <*> sequenceA [ toRef sv ]
eFieldDecl (FieldDeclReference _fv _fvWf) =
  error "KnotCore.Elaboration.Size.eFieldDecl: NOT IMPLEMENTED"
