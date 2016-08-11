{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module KnotCore.Elaboration.SubstEnvRelation where

import Control.Applicative
import Data.Maybe

import Coq.StdLib
import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core

eSubstEnvRelationss :: Elab m => [EnvDecl] -> m [Sentence]
eSubstEnvRelationss = fmap concat . traverse eSubstEnvRelations

eSubstEnvRelations :: Elab m => EnvDecl -> m [Sentence]
eSubstEnvRelations (EnvDecl etn _ ecs) =
  concat <$> sequenceA
    [ localNames $ do
        henv     <- freshEnvVariable etn
        (stn,_)  <- getNamespaceCtor hntn
        ht       <- freshSortVariable stn
        hfields' <- freshen hfields

        eSubstEnvRelation henv hcn hntn hfields' ht ecs
    | EnvCtorCons hcn hmv hfields _mbRtn <- ecs
    , let hntn = typeNameOf hmv
    ]

eSubstEnvRelation ::
  Elab m => EnvVariable -> CtorName -> NamespaceTypeName ->
  [FieldDecl 'WOMV] -> SortVariable -> [EnvCtor] -> m [Sentence]
eSubstEnvRelation henv hcn hntn hfields ht ecs =
  sequenceA [ eDeclaration, eWeakenSubstEnv ]
  where
    etn :: EnvTypeName
    etn = typeNameOf henv

    eDeclaration :: Elab m => m Sentence
    eDeclaration = do
      ecs' <- freshen' ecs
      body <-
        InductiveBody
          <$> idTypeSubstEnv hcn
          <*> sequenceA
              ([toBinder henv] ++
               eFieldDeclBinders hfields ++
               [toBinder ht]
              )
          <*> (prop
               <$> sequenceA
                   [ typeTrace hntn
                   , toRef etn
                   , toRef etn
                   ]
               )
          <*> sequenceA
              (eSubstEnvHere:
               [ eSubstEnvThere tcn tntn tfields
               | EnvCtorCons tcn tmv tfields _mbRtn <- ecs'
               , let tntn = typeNameOf tmv
               ]
              )

      return $ SentenceInductive (Inductive [body])

    eSubstEnvHere :: Elab m => m InductiveCtor
    eSubstEnvHere = localNames $ do
      hfs <- eFieldDeclFields hfields

      InductiveCtor
        <$> idCtorSubstEnvHere hcn
        <*> pure []
        <*> (Just
             <$> toTerm (SubstEnv
                          (EVar henv)
                          hfs
                          (SVar ht)
                          (T0 hntn)
                          (ECons (EVar henv) hntn hfs)
                          (EVar henv)
                        )
            )

    eSubstEnvThere :: Elab m => CtorName -> NamespaceTypeName ->
      [FieldDecl 'WOMV] -> m InductiveCtor
    eSubstEnvThere tcn tntn tfields = localNames $ do

      x       <- freshTraceVar hntn
      ev1     <- freshEnvVariable etn
      ev2     <- freshEnvVariable etn

      hfs <- eFieldDeclFields hfields
      tfs <- eFieldDeclFields tfields

      premise <- toTerm
                 (SubstEnv
                    (EVar henv)
                    hfs
                    (SVar ht)
                    (TVar x)
                    (EVar ev1)
                    (EVar ev2)
                 )
      concl   <- toTerm
                 (SubstEnv
                    (EVar henv)
                    hfs
                    (SVar ht)
                    (TS tntn (TVar x))
                    (ECons (EVar ev1) tntn tfs)
                    (ECons (EVar ev2) tntn (map (substField (TVar x) (SVar ht)) tfs))
                 )

      InductiveCtor
        <$> idCtorSubstEnvThere hcn tcn
        <*> sequenceA (toImplicitBinder x:
                      toImplicitBinder ev1:
                      toImplicitBinder ev2:
                      eFieldDeclBinders tfields)
        <*> pure (Just $ TermFunction premise concl)

    eWeakenSubstEnv :: Elab m => m Sentence
    eWeakenSubstEnv = localNames $ do

      lemma <- idLemmaWeakenSubstEnv hcn
      delta <- freshEnvVariable etn
      x     <- freshTraceVar hntn
      ev1   <- freshEnvVariable etn
      ev2   <- freshEnvVariable etn

      binders   <- sequenceA
                   ([ toImplicitBinder henv ] ++
                    eFieldDeclBinders hfields ++
                    [ toImplicitBinder ht ]
                   )

      fs <- eFieldDeclFields hfields

      statement <- TermForall
                   <$> sequenceA
                       [ toBinder delta
                       , toImplicitBinder x
                       , toImplicitBinder ev1
                       , toImplicitBinder ev2
                       ]
                   <*> (TermFunction
                        <$> toTerm
                            (SubstEnv
                              (EVar henv)
                              fs
                              (SVar ht)
                              (TVar x)
                              (EVar ev1)
                              (EVar ev2))
                        <*> toTerm
                            (SubstEnv
                              (EVar henv)
                              fs
                              (SVar ht)
                              (TWeaken (TVar x) (HVDomainEnv (EVar delta)))
                              (EAppend (EVar ev1) (EVar delta))
                              (EAppend (EVar ev2) (ESubst' (TVar x) (SVar ht) (EVar delta)))
                            )
                       )

      return $
        SentenceAssertionProof
          (Assertion AssLemma lemma binders statement)
          (ProofQed [PrTactic "needleGenericWeakenSubstEnv" []])
