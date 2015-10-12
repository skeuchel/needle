
module KnotCore.Elaboration.Functions where

import Control.Applicative
import Data.Maybe (catMaybes)

import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core

eFunGroupDecls :: Elab m => [FunGroupDecl] -> m [Sentence]
eFunGroupDecls fgds = concat <$> mapM eFunGroupDecl fgds

eFunGroupDecl :: Elab m => FunGroupDecl -> m [Sentence]
eFunGroupDecl (FunGroupDecl fgn _ fdss) = do
  fixpoint <-
    SentenceFixpoint . Fixpoint
      <$> sequence [ eFunDecl fd | (_,fds) <- fdss, fd <- fds ]
  let stns = [ stn | (stn,_) <- fdss ]
  inductions <- eSchemeSortGroupDecl fgn stns
  return (fixpoint:inductions)

eFunDecl :: Elab m => FunDecl -> m FixpointBody
eFunDecl (FunDecl fn _ _ matchItem cases) =
    FixpointBody
      <$> toId fn
      <*> sequence [ toBinder matchItem ]
      <*> (Just . Struct <$> toId matchItem)
      <*> (idTypeHVarlist >>= toRef)
      <*> (TermMatch
             <$> (MatchItem
                    <$> toRef matchItem
                    <*> pure Nothing
                    <*> pure Nothing)
             <*> pure Nothing
             <*> mapM eFunCase cases
          )

eFunCase :: Elab m => FunCase -> m Equation
eFunCase (FunCase cn fields rhs) =
  Equation
    <$> (PatCtor
           <$> (Ident <$> toId cn)
           <*> eFieldMetaIdentifiers fields)
    <*> toTerm (evalBindSpec rhs)

eFieldMetaIdentifiers :: Elab m => [FieldMetaBinding] -> m [Identifier]
eFieldMetaIdentifiers = fmap catMaybes . mapM eFieldMetaIdentifier

eFieldMetaIdentifier :: Elab m => FieldMetaBinding -> m (Maybe Identifier)
eFieldMetaIdentifier (FieldMetaBindingSubtree sv) = Just <$> toId sv
eFieldMetaIdentifier (FieldMetaBindingMetavar _)  = pure Nothing
eFieldMetaIdentifier (FieldMetaBindingOutput ev)  = Just <$> toId ev

eSchemeSortGroupDecl :: Elab m => FunGroupName -> [SortTypeName] -> m [Sentence]
eSchemeSortGroupDecl fgn stns =
  do
    let sgtn = groupName stns

    individual <- SentenceScheme . Scheme
                    <$> mapM (eSchemeSortDecl fgn) stns
    group      <- SentenceCombinedScheme
                    <$> idFunctionInductionSortGroup fgn sgtn
                    <*> mapM (idFunctionInductionSort fgn) stns
    case stns of
      [_] -> return [individual]
      _   -> return [individual,group]

eSchemeSortDecl :: Elab m => FunGroupName -> SortTypeName -> m SchemeBody
eSchemeSortDecl fgn stn =
  SchemeInduction
    <$> idFunctionInductionSort fgn stn
    <*> toId stn
