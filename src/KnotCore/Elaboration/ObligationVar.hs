{-# LANGUAGE DataKinds #-}

module KnotCore.Elaboration.ObligationVar where

import Coq.StdLib
import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core

import Control.Applicative

obligations :: Elab m => [EnvDecl] -> m [Sentence]
obligations eds = concat <$> sequenceA
  [ eEnvDecl (typeNameOf ed) (typeNameOf bv) rtn fds
  | ed <- eds
  , EnvCtorCons _cn bv fds (Just (EnvCtorSubst rtn Nothing)) <- edCtors ed
  ]

eEnvDecl :: Elab m => EnvTypeName -> NamespaceTypeName -> RelationTypeName -> [FieldDecl 'WOMV] -> m [Sentence]
eEnvDecl etn ntn rtn fds = do
  ev <-freshEnvVariable etn
  iv <- freshIndexVar ntn
  fs <- eFieldDeclFields fds
  (stn,cn) <- getNamespaceCtor ntn

  methodDecl <-
    MethodDeclaration
    <$> idMethodObligationVar etn ntn
    <*> sequenceA (toBinder ev:toBinder iv:eFieldDeclBinders fds)
    <*> (TermFunction
         <$> toTerm (Lookup (EVar ev) (IVar iv) fs)
         <*> toTerm (PJudgement rtn (JudgementEnvTerm (EVar ev))
                     (FieldSort (SCtorVar stn cn (IVar iv)): fs) []
                    )
        )

  classDecl <-
    ClassDeclaration
    <$> idClassObligationVar etn ntn
    <*> pure []
    <*> pure (Just Prop)
    <*> pure [methodDecl]
  classRef <- idClassObligationVar etn ntn >>= toRef
  inst <- idInstObligationVar  etn ntn

  return
    [ SentenceClassDecl classDecl
    , SentenceContext [BinderImplicitNameType [NameIdent inst] classRef]
    ]
