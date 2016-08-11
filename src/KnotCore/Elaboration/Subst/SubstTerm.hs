{-# LANGUAGE GADTs #-}

module KnotCore.Elaboration.Subst.SubstTerm where

import qualified Coq.Syntax as Coq

import KnotCore.Syntax
import KnotCore.Elaboration.Core

import Control.Applicative
import Control.Monad
import Data.Maybe


eSortGroupDecls :: Elab m => [SortGroupDecl] -> m [Coq.Sentence]
eSortGroupDecls sgs = concat <$> traverse eSortGroupDecl sgs

eSortGroupDecl :: Elab m => SortGroupDecl -> m [Coq.Sentence]
eSortGroupDecl sg =
  sequenceA
    [ Coq.SentenceFixpoint . Coq.Fixpoint <$> traverse (eSortDecl ntn) (sgSorts sg)
    | ntn <- sgNamespaces sg
    ]

eSortDecl :: Elab m => NamespaceTypeName -> SortDecl -> m Coq.FixpointBody
eSortDecl ntn (SortDecl stn' _ ctors) = localNames $ do
  (stn,_) <- getNamespaceCtor ntn

  subst   <- idFunctionSubst ntn stn'
  x       <- freshTraceVar ntn
  s       <- freshSortVariable stn
  t       <- freshSortVariable stn'

  binders <- sequenceA [toBinder x, toBinder s, toBinder t]
  anno    <- Just . Coq.Struct <$> toId t
  retType <- toRef (typeNameOf t)
  body    <-
    Coq.TermMatch
    <$> (Coq.MatchItem <$> toRef t <*> pure Nothing <*> pure Nothing)
    <*> pure Nothing
    <*> traverse (freshen >=> eCtorDecl x s) ctors
  return $ Coq.FixpointBody subst binders anno retType body

eCtorDecl :: Elab m => TraceVar -> SortVariable -> CtorDecl -> m Coq.Equation
eCtorDecl x s (CtorVar cn mv _) = do
  y       <- toIndex mv
  pattern <- Coq.PatCtor
             <$> toQualId cn
             <*> sequenceA [ toId y ]

  rhs     <- if typeNameOf x == typeNameOf y
             then Coq.TermApp
                  <$> (idFunctionSubstIndex (typeNameOf mv) >>= toRef)
                  <*> sequenceA [ toRef x, toRef s, toRef y ]
             else Coq.TermApp
                  <$> toRef cn
                  <*> sequenceA [ toRef y ]
  return $ Coq.Equation pattern rhs
eCtorDecl x s (CtorReg cn fields) = do
  pattern <- Coq.PatCtor
             <$> toQualId cn
             <*> sequenceA (eFieldDeclIdentifiers fields)
  rhs     <- Coq.TermApp
             <$> toRef cn
             <*> eFieldDecls x s fields
  return $ Coq.Equation pattern rhs

eFieldDecls :: Elab m => TraceVar -> SortVariable -> [FieldDecl w] -> m Coq.Terms
eFieldDecls x s = fmap catMaybes . traverse (eFieldDecl x s)

eFieldDecl :: Elab m => TraceVar -> SortVariable -> FieldDecl w -> m (Maybe Coq.Term)
eFieldDecl _ _ (FieldDeclBinding _bs _bv) = pure Nothing
eFieldDecl x s (FieldDeclSort bs sv _svWf) = fmap Just $
  do
    let ntn = typeNameOf x
        stn = typeNameOf sv
    deps      <- getSortNamespaceDependencies stn
    if ntn `elem` deps
      then Coq.TermApp
             <$> (idFunctionSubst ntn stn >>= toRef)
             <*> sequenceA
                   [ toTerm (simplifyTrace (TWeaken (TVar x) (evalBindSpec HV0 bs)))
                   , toRef s
                   , toRef sv
                   ]
      else toRef sv
eFieldDecl _ _ (FieldDeclReference _fv _fvWf) =
  error "KnotCore.Elaboration.Subst.SubstTerm.eFieldDecl.FieldReference: impossible"
