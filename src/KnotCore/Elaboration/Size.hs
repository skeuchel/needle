
module KnotCore.Elaboration.Size where

import Control.Applicative
import Data.Maybe

import qualified Coq.StdLib as Coq
import qualified Coq.Syntax as Coq

import KnotCore.Syntax
import KnotCore.Elaboration.Core

eSortGroupDecls :: Elab m => [SortGroupDecl] -> m [Coq.Sentence]
eSortGroupDecls sgs = mapM eSortGroupDecl sgs

eSortGroupDecl :: Elab m => SortGroupDecl -> m Coq.Sentence
eSortGroupDecl sg =
  Coq.SentenceFixpoint . Coq.Fixpoint
  <$> mapM eSortDecl (sgSorts sg)

eSortDecl :: Elab m => SortDecl -> m Coq.FixpointBody
eSortDecl (SortDecl stn _ ctors) = localNames $
  do
    size       <- idFunctionSize stn
    matchItem  <- freshSubtreeVar stn
    binders    <- sequence [ toBinder matchItem ]
    anno       <- Just . Coq.Struct <$> toId matchItem
    retType    <- pure Coq.nat
    body       <-
      Coq.TermMatch
        <$> (Coq.MatchItem
               <$> toRef matchItem
               <*> pure Nothing
               <*> pure Nothing)
        <*> pure Nothing
        <*> mapM (\cd -> freshen cd >>= eCtorDecl) ctors
    return $ Coq.FixpointBody size binders anno retType body

eCtorDecl :: Elab m => CtorDecl -> m Coq.Equation
eCtorDecl (CtorVar cn mv) =
  do
    index   <- toIndex mv
    pattern <- Coq.PatCtor
                 <$> toQualId cn
                 <*> sequence [ toId index ]
    return $ Coq.Equation pattern (Coq.TermNum 1)
eCtorDecl (CtorTerm cn fields) =
  do
    pattern <- Coq.PatCtor
                 <$> toQualId cn
                 <*> eFieldDeclIdentifiers fields
    sizes  <- eFieldDecls fields
    let rhs = foldr1 Coq.plus (Coq.TermNum 1:sizes)
    return $ Coq.Equation pattern rhs

eFieldDeclIdentifiers :: Elab m => [FieldDecl] -> m Coq.Identifiers
eFieldDeclIdentifiers = fmap catMaybes . mapM eFieldDeclIdentifier

eFieldDeclIdentifier :: Elab m => FieldDecl -> m (Maybe Coq.Identifier)
eFieldDeclIdentifier (FieldSubtree sn _) = Just <$> toId sn
eFieldDeclIdentifier (FieldBinding _)    = pure Nothing

eFieldDecls :: Elab m => [FieldDecl] -> m Coq.Terms
eFieldDecls = fmap catMaybes . mapM eFieldDecl

eFieldDecl :: Elab m => FieldDecl -> m (Maybe Coq.Term)
eFieldDecl (FieldBinding _)    = pure Nothing
eFieldDecl (FieldSubtree sn _) = fmap Just $
  Coq.TermApp
    <$> (idFunctionSize (typeNameOf sn) >>= toRef)
    <*> sequence [ toRef sn ]
