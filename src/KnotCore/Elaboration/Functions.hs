
module KnotCore.Elaboration.Functions where

import Control.Applicative
import Data.Maybe (catMaybes)

import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core

eFunGroupDecls :: Elab m => [FunGroupDecl] -> m [Sentence]
eFunGroupDecls fgds = concat <$> traverse eFunGroupDecl fgds

eFunGroupDecl :: Elab m => FunGroupDecl -> m [Sentence]
eFunGroupDecl (FunGroupDecl fgn _ fdss) = do
  fixpoint <-
    SentenceFixpoint . Fixpoint
      <$> sequenceA [ eFunDecl fd | (_,fds) <- fdss, fd <- fds ]
  let stns = [ stn | (stn,_) <- fdss ]
  inductions <- eSchemeSortGroupDecl fgn stns
  return (fixpoint:inductions)

eFunDecl :: Elab m => FunDecl -> m FixpointBody
eFunDecl (FunDecl fn stn _ cases) = do
  matchItem <- freshSortVariable stn
  FixpointBody
    <$> toId fn
    <*> sequenceA [ toBinder matchItem ]
    <*> (Just . Struct <$> toId matchItem)
    <*> (idTypeHVarlist >>= toRef)
    <*> (TermMatch
           <$> (MatchItem
                  <$> toRef matchItem
                  <*> pure Nothing
                  <*> pure Nothing)
           <*> pure Nothing
           <*> traverse eFunCase cases
        )

eFunCase :: Elab m => FunCase -> m Equation
eFunCase (FunCase cn fields rhs) =
  Equation
    <$> (PatCtor
           <$> (Ident <$> toId cn)
           <*> eFieldMetaIdentifiers fields)
    <*> toTerm (evalBindSpec HV0 rhs)

eFieldMetaIdentifiers :: Elab m => [FunField] -> m [Identifier]
eFieldMetaIdentifiers = fmap catMaybes . traverse eFieldMetaIdentifier

eFieldMetaIdentifier :: Elab m => FunField -> m (Maybe Identifier)
eFieldMetaIdentifier (FunFieldSort _bs sv)     = Just <$> toId sv
eFieldMetaIdentifier (FunFieldBinding _bs _bv) = pure Nothing
eFieldMetaIdentifier (FunFieldEnv _bs ev)      = Just <$> toId ev
eFieldMetaIdentifier (FunFieldReference _fv)   =
  error "KnotCore.Elaboration.eFieldMetaIdentifier.FunFieldReference: NOT IMPLEMENTED"

eSchemeSortGroupDecl :: Elab m => FunGroupName -> [SortTypeName] -> m [Sentence]
eSchemeSortGroupDecl fgn stns =
  do
    let sgtn = groupName stns

    individual <- SentenceScheme . Scheme
                    <$> traverse (eSchemeSortDecl fgn) stns
    group      <- SentenceCombinedScheme
                    <$> idFunctionInductionSortGroup fgn sgtn
                    <*> traverse (idFunctionInductionSort fgn) stns
    case stns of
      [_] -> return [individual]
      _   -> return [individual,group]

eSchemeSortDecl :: Elab m => FunGroupName -> SortTypeName -> m SchemeBody
eSchemeSortDecl fgn stn =
  SchemeInduction
    <$> idFunctionInductionSort fgn stn
    <*> toId stn
