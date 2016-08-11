{-# LANGUAGE GADTs #-}

module KnotCore.Elaboration.Shift.ShiftTerm where

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
eSortDecl ntn (SortDecl stn _ ctors) = localNames $
  do
    cutoff     <- freshCutoffVar ntn
    matchItem  <- freshSortVariable stn
    shift      <- idFunctionShift ntn stn
    binders    <- sequenceA [ toBinder cutoff, toBinder matchItem ]
    anno       <- Just . Coq.Struct <$> toId matchItem
    retType    <- toRef (typeNameOf matchItem)
    body       <-
      Coq.TermMatch
        <$> (Coq.MatchItem
               <$> toRef matchItem
               <*> pure Nothing
               <*> pure Nothing)
        <*> pure Nothing
        <*> traverse (freshen >=> eCtorDecl cutoff) ctors
    return $ Coq.FixpointBody shift binders anno retType body

eCtorDecl :: Elab m => CutoffVar -> CtorDecl -> m Coq.Equation
eCtorDecl co (CtorVar cn mv _) =
  do
    index   <- toIndex mv
    pattern <- Coq.PatCtor
                 <$> toQualId cn
                 <*> sequenceA [ toId index ]
    ctor    <- toRef cn
    arg     <- if typeNameOf co == typeNameOf mv
               then Coq.TermApp
                      <$> (idFunctionShiftIndex (typeNameOf mv) >>= toRef)
                      <*> sequenceA [ toRef co, toRef index ]
               else toRef index
    return $ Coq.Equation pattern (Coq.TermApp ctor [arg])
eCtorDecl co (CtorReg cn fields) =
  do
    pattern <- Coq.PatCtor
                 <$> toQualId cn
                 <*> sequenceA (eFieldDeclIdentifiers fields)
    rhs     <- Coq.TermApp
                 <$> toRef cn
                 <*> eFieldDecls co fields
    return $ Coq.Equation pattern rhs

eFieldDecls :: Elab m => CutoffVar -> [FieldDecl w] -> m Coq.Terms
eFieldDecls co = fmap catMaybes . traverse (eFieldDecl co)

eFieldDecl :: Elab m => CutoffVar -> FieldDecl w -> m (Maybe Coq.Term)
eFieldDecl _  (FieldDeclBinding _bs _bv)  = pure Nothing
eFieldDecl co (FieldDeclSort bs sv _svWf) = fmap Just $
  do
    let stn = typeNameOf sv
    deps      <- getSortNamespaceDependencies stn
    if typeNameOf co `elem` deps
      then Coq.TermApp
             <$> (idFunctionShift (typeNameOf co) stn >>= toRef)
             <*> sequenceA
                 [ toTerm (simplifyCutoff (CWeaken (CVar co) (evalBindSpec HV0 bs)))
                 , toRef sv
                 ]
      else toRef sv
eFieldDecl _ (FieldDeclReference _fv _fvWf) =
  error "KnotCore.Elaboration.Shift.ShiftTerm.eFieldDecl.FieldReference: not implemented"
