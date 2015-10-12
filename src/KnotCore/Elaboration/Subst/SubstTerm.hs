
module KnotCore.Elaboration.Subst.SubstTerm where

import Control.Applicative
import Data.Maybe

import qualified Coq.Syntax as Coq

import KnotCore.Syntax
import KnotCore.Elaboration.Core

eSortGroupDecls :: Elab m => [SortGroupDecl] -> m [Coq.Sentence]
eSortGroupDecls sgs = concat <$> mapM eSortGroupDecl sgs

eSortGroupDecl :: Elab m => SortGroupDecl -> m [Coq.Sentence]
eSortGroupDecl sg =
  sequence
    [ Coq.SentenceFixpoint . Coq.Fixpoint <$> mapM (eSortDecl ntn) (sgSorts sg)
    | ntn <- sgNamespaces sg
    ]

eSortDecl :: Elab m => NamespaceTypeName -> SortDecl -> m Coq.FixpointBody
eSortDecl ntn (SortDecl stn' _ ctors) = localNames $ do
  (stn,_) <- getNamespaceCtor ntn

  subst   <- idFunctionSubst ntn stn'
  x       <- freshTraceVar ntn
  s       <- freshSubtreeVar stn
  t       <- freshSubtreeVar stn'

  binders <- sequence [toBinder x, toBinder s, toBinder t]
  anno    <- Just . Coq.Struct <$> toId t
  retType <- toRef (typeNameOf t)
  body    <-
    Coq.TermMatch
    <$> (Coq.MatchItem <$> toRef t <*> pure Nothing <*> pure Nothing)
    <*> pure Nothing
    <*> mapM (\cd -> freshen cd >>= eCtorDecl x s) ctors
  return $ Coq.FixpointBody subst binders anno retType body

eCtorDecl :: Elab m => TraceVar -> SubtreeVar -> CtorDecl -> m Coq.Equation
eCtorDecl x s (CtorVar cn mv) = do
  y       <- toIndex mv
  pattern <- Coq.PatCtor
             <$> toQualId cn
             <*> sequence [ toId y ]

  rhs     <- if typeNameOf x == typeNameOf y
             then Coq.TermApp
                  <$> (idFunctionSubstIndex (typeNameOf mv) >>= toRef)
                  <*> sequence [ toRef x, toRef s, toRef y ]
             else Coq.TermApp
                  <$> toRef cn
                  <*> sequence [ toRef y ]
  return $ Coq.Equation pattern rhs
eCtorDecl x s (CtorTerm cn fields) = do
  pattern <- Coq.PatCtor
             <$> toQualId cn
             <*> eFieldDeclIdentifiers fields
  rhs     <- Coq.TermApp
             <$> toRef cn
             <*> eFieldDecls x s fields
  return $ Coq.Equation pattern rhs

eFieldDeclIdentifiers :: Elab m => [FieldDecl] -> m Coq.Identifiers
eFieldDeclIdentifiers = fmap catMaybes . mapM eFieldDeclIdentifier

eFieldDeclIdentifier :: Elab m => FieldDecl -> m (Maybe Coq.Identifier)
eFieldDeclIdentifier (FieldSubtree t _) = Just <$> toId t
eFieldDeclIdentifier (FieldBinding _)   = pure Nothing

eFieldDecls :: Elab m => TraceVar -> SubtreeVar -> [FieldDecl] -> m Coq.Terms
eFieldDecls x s = fmap catMaybes . mapM (eFieldDecl x s)

eFieldDecl :: Elab m => TraceVar -> SubtreeVar -> FieldDecl -> m (Maybe Coq.Term)
eFieldDecl _ _ (FieldBinding _)    = pure Nothing
eFieldDecl x s (FieldSubtree t bs) = fmap Just $
  do
    let ntn = typeNameOf x
        stn = typeNameOf t
    deps      <- getSortNamespaceDependencies stn
    if ntn `elem` deps
      then Coq.TermApp
             <$> (idFunctionSubst ntn stn >>= toRef)
             <*> sequence [ toTerm (liftTraceVar bs x), toRef s, toRef t ]
      else toRef t
