
module KnotCore.Elaboration.Shift.ShiftTerm where

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
eSortDecl ntn (SortDecl stn _ ctors) = localNames $
  do
    cutoff     <- freshCutoffVar ntn
    matchItem  <- freshSubtreeVar stn
    shift      <- idFunctionShift ntn stn
    binders    <- sequence [ toBinder cutoff, toBinder matchItem ]
    anno       <- Just . Coq.Struct <$> toId matchItem
    retType    <- toRef (typeNameOf matchItem)
    body       <-
      Coq.TermMatch
        <$> (Coq.MatchItem
               <$> toRef matchItem
               <*> pure Nothing
               <*> pure Nothing)
        <*> pure Nothing
        <*> mapM (\cd -> freshen cd >>= eCtorDecl cutoff) ctors
    return $ Coq.FixpointBody shift binders anno retType body

eCtorDecl :: Elab m => CutoffVar -> CtorDecl -> m Coq.Equation
eCtorDecl co (CtorVar cn mv) =
  do
    index   <- toIndex mv
    pattern <- Coq.PatCtor
                 <$> toQualId cn
                 <*> sequence [ toId index ]
    ctor    <- toRef cn
    arg     <- if typeNameOf co == typeNameOf mv
               then Coq.TermApp
                      <$> (idFunctionShiftIndex (typeNameOf mv) >>= toRef)
                      <*> sequence [ toRef co, toRef index ]
               else toRef index
    return $ Coq.Equation pattern (Coq.TermApp ctor [arg])
eCtorDecl co (CtorTerm cn fields) =
  do
    pattern <- Coq.PatCtor
                 <$> toQualId cn
                 <*> eFieldDeclIdentifiers fields
    rhs     <- Coq.TermApp
                 <$> toRef cn
                 <*> eFieldDecls co fields
    return $ Coq.Equation pattern rhs

eFieldDeclIdentifiers :: Elab m => [FieldDecl] -> m Coq.Identifiers
eFieldDeclIdentifiers = fmap catMaybes . mapM eFieldDeclIdentifier

eFieldDeclIdentifier :: Elab m => FieldDecl -> m (Maybe Coq.Identifier)
eFieldDeclIdentifier (FieldSubtree sn _) = Just <$> toId sn
eFieldDeclIdentifier (FieldBinding _)    = pure Nothing

eFieldDecls :: Elab m => CutoffVar -> [FieldDecl] -> m Coq.Terms
eFieldDecls co = fmap catMaybes . mapM (eFieldDecl co)

eFieldDecl :: Elab m => CutoffVar -> FieldDecl -> m (Maybe Coq.Term)
eFieldDecl _  (FieldBinding _)    = pure Nothing
eFieldDecl co (FieldSubtree sn bs) = fmap Just $
  do
    let stn = typeNameOf sn
    deps      <- getSortNamespaceDependencies stn
    if typeNameOf co `elem` deps
      then Coq.TermApp
             <$> (idFunctionShift (typeNameOf co) stn >>= toRef)
             <*> sequence [ toTerm (liftCutoffVar bs co), toRef sn ]
      else toRef sn
