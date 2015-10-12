

module KnotCore.Elaboration.Relation where

import Control.Applicative
import Control.Monad
import Data.Maybe

import qualified Coq.StdLib as Coq
import qualified Coq.Syntax as Coq

import KnotCore.Syntax
import KnotCore.Elaboration.Core

eIndexType :: Elab m => MbEnvName -> SortTypeName -> m Coq.Terms
eIndexType mbEnvName stn =
  do
    fns <- getFunctionNames stn
    index   <- sortType stn
    outputs <- sequence [ eMbEnvNameType mbEnvName | fn <- fns ]
    return $ index : concat outputs


eRelationType :: Elab m => MbEnvName -> SortTypeNames -> m Coq.Term
eRelationType mbEnvName indices =
  Coq.prop . concat <$> mapM (eIndexType mbEnvName) indices

eRelationDecl :: Elab m => RelationDecl -> m Coq.Sentence
eRelationDecl (RelationDecl mbEnvName rtn indices rules) =
  do
    body <- Coq.InductiveBody
              <$> relationIdentifier rtn
              <*> eMbEnvNameBinder mbEnvName
              <*> eRelationType mbEnvName indices
              <*> mapM (eRule mbEnvName) rules
    return . Coq.SentenceInductive $ Coq.Inductive [ body ]

eRule :: Elab m => MbEnvName -> Rule -> m Coq.InductiveCtor
eRule mbEnvName (Rule cn metaBinds prem conc rbinds) =
  Coq.InductiveCtor
    <$> ctorIdentifier cn
    <*> eFieldMetaBinders metaBinds
    <*> (fmap Just $ Coq.relation
           <$> mapM (eFormula mbEnvName) prem
           <*> eJudgement mbEnvName conc
        )

eFieldMetaBinders :: Elab m => FieldMetaBindings -> m Coq.Binders
eFieldMetaBinders = mapM eFieldMetaBinder

eFieldMetaBinder :: Elab m => FieldMetaBinding -> m Coq.Binder
eFieldMetaBinder (FieldMetaBindingSubtree sn) = subtreeBinder sn
eFieldMetaBinder (FieldMetaBindingMetavar mv) = metavarBinder mv
eFieldMetaBinder (FieldMetaBindingOutput en) = envNameBinder en


{-

eCtorDecl :: Elab m => CtorDecl -> m Coq.InductiveCtor
eCtorDecl (CtorVar cn mv)      =
  Coq.InductiveCtor
    <$> ctorIdentifier cn
    <*> sequence [ metavarBinder mv ] -- Single Field
    <*> pure Nothing                  -- Normal ADT constructor
eCtorDecl (CtorTerm cn fields) =
  Coq.InductiveCtor
    <$> ctorIdentifier cn
    <*> (catMaybes <$> mapM eFieldDecl fields)
    <*> pure Nothing                  -- Normal ADT constructor

eFieldDecl :: Elab m => FieldDecl -> m (Maybe Coq.Binder)
eFieldDecl (FieldSubtree name _) = Just <$> subtreeBinder name
eFieldDecl (FieldBinding name)   = return Nothing

eFieldMetaIdentifiers :: Elab m => FieldMetaBindings -> m Coq.Identifiers
eFieldMetaIdentifiers = fmap catMaybes . mapM eFieldMetaIdentifier

eFieldMetaIdentifier :: Elab m => FieldMetaBinding -> m (Maybe Coq.Identifier)
eFieldMetaIdentifier (FieldMetaBindingSubtree sn) = Just <$> subtreeIdentifier sn
eFieldMetaIdentifier (FieldMetaBindingMetavar mv) = pure Nothing

-- eFieldMetaBinders :: Elab m => FieldMetaBindings -> m Coq.Binders
-- eFieldMetaBinders = fmap catMaybes . mapM eFieldMetaBinder
--
-- eFieldMetaBinder :: Elab m => FieldMetaBinding -> m (Maybe Coq.Binder)
-- eFieldMetaBinder (FieldMetaBindingSubtree sn) = Just <$> subtreeBinder sn
-- eFieldMetaBinder (FieldMetaBindingMetavar mv) = pure Nothing

eEnvDecl :: Elab m => EnvDecl -> m Coq.Sentence
eEnvDecl (EnvDecl etn _ ctors) =
  fmap (Coq.SentenceInductive .
        Coq.Inductive . (:[])) $
    Coq.InductiveBody
      <$> envIdentifier etn
      <*> pure []
      <*> pure (Coq.TermSort Coq.Set)
      <*> ((:)
             <$> (-- Nil env constructor
                  Coq.InductiveCtor
                    <$> nameEnvNil etn -- Constructor name
                    <*> pure []        -- No fields
                    <*> pure Nothing   -- Normal ADT constructor
                 )
             <*> mapM eEnvCtor ctors)
  where
    eEnvCtor :: Elab m => EnvCtor -> m Coq.InductiveCtor
    eEnvCtor (EnvCtorTerm cn mv pr fields) =
      Coq.InductiveCtor
        <$> ctorIdentifier cn
        <*> ((:)
               <$> envNameBinder pr
               <*> mapM subtreeBinder fields
            )
        <*> pure Nothing      -- Normal ADT constructor.

eFunDecl :: Elab m => FunDecl -> m Coq.Sentence
eFunDecl (FunDecl fn _ _ matchItem cases) =
  fmap (Coq.SentenceFixpoint . Coq.Fixpoint . (:[])) $
    Coq.FixpointBody
      <$> functionIdentifier fn
      <*> sequence [ subtreeBinder matchItem ]
      <*> (Just . Coq.Struct <$> subtreeIdentifier matchItem)
      <*> pure Coq.nat
      <*> (Coq.TermMatch
             <$> (Coq.MatchItem
                    <$> subtreeRef matchItem
                    <*> pure Nothing
                    <*> pure Nothing)
             <*> pure Nothing
             <*> mapM eFunCase cases
          )

eFunCase :: Elab m => FunCase -> m Coq.Equation
eFunCase (FunCase cn fields rhs) =
  Coq.Equation
    <$> (Coq.PatCtor
           <$> (Coq.Ident <$> ctorIdentifier cn)
           <*> eFieldMetaIdentifiers fields)
    <*> eVleNat rhs

eVleNat :: Elab m => Vle -> m Coq.Term
eVleNat [] = return Coq.termZero
eVleNat vs = foldr1 Coq.plus . reverse <$> mapM eVleItemNat vs

eVleItemNat :: Elab m => VleItem -> m Coq.Term
eVleItemNat (VleBinding mv) = return $ Coq.TermNum 1
eVleItemNat (VleCall fn sn) =
  Coq.TermApp
    <$> functionRef fn
    <*> sequence [ subtreeRef sn ]
-}
