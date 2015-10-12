{-# LANGUAGE ScopedTypeVariables #-}

module KnotCore.Elaboration.InsertEnvRelation where

import Control.Applicative
import Data.Maybe

import Coq.StdLib
import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core

eInsertEnvRelationss :: Elab m => [EnvDecl] -> m [Sentence]
eInsertEnvRelationss = fmap concat . mapM eInsertEnvRelations

eInsertEnvRelations :: Elab m => EnvDecl -> m [Sentence]
eInsertEnvRelations (EnvDecl etn _ ecs) =
  concat <$> sequence
    [ localNames $ do
        hfields' <- freshen hfields
        eInsertEnvRelation etn hcn hntn hfields' ecs
    | EnvCtorCons hcn hmv hfields <- ecs
    , let hntn = typeNameOf hmv
    ]

eInsertEnvRelation ::
  forall m. Elab m =>
  EnvTypeName ->
  CtorName -> NamespaceTypeName -> [SubtreeVar] ->
  [EnvCtor] -> m [Sentence]
eInsertEnvRelation etn hcn hntn hfields ecs = sequence [ eDeclaration, eWeakenInsert ]
  where
    eDeclaration :: m Sentence
    eDeclaration = do
      body <-
        InductiveBody
          <$> idTypeInsertEnv hcn
          <*> pure []
          <*> (prop <$> sequence [typeCutoff hntn, toRef etn, toRef etn])
          <*> sequence
              (eInsertEnvHere:
               [ eInsertEnvThere tcn tntn tfields
               | EnvCtorCons tcn tmv tfields <- ecs
               , let tntn = typeNameOf tmv
               ]
              )

      return $ SentenceInductive (Inductive [body])

    eInsertEnvHere :: m InductiveCtor
    eInsertEnvHere = localNames $ do

      ev     <- freshEnvVar etn

      InductiveCtor
        <$> idCtorInsertEnvHere hcn
        <*> sequence (toImplicitBinder ev:map toImplicitBinder hfields)
        <*> (Just
             <$> toTerm (InsertEnv
                          (C0 hntn)
                          (EVar ev)
                          (ECtor hcn (EVar ev) (map SVar hfields))
                        )
            )

    eInsertEnvThere :: CtorName -> NamespaceTypeName -> [SubtreeVar] -> m InductiveCtor
    eInsertEnvThere tcn tntn tfields = localNames $ do

      c       <- freshCutoffVar hntn
      ev1     <- freshEnvVar etn
      ev2     <- freshEnvVar etn

      premise <- toTerm (InsertEnv (CVar c) (EVar ev1) (EVar ev2))
      concl   <- toTerm (InsertEnv
                           (CS' tntn (CVar c))
                           (ECtor tcn (EVar ev1) (map SVar tfields))
                           (ECtor tcn (EVar ev2) (map (SShift' (CVar c) . SVar) tfields)))

      InductiveCtor
        <$> idCtorInsertEnvThere hcn tcn
        <*> sequence (toImplicitBinder c:
                      toImplicitBinder ev1:
                      toImplicitBinder ev2:
                      map toImplicitBinder tfields)
        <*> pure (Just $ TermFunction premise concl)


    eWeakenInsert :: m Sentence
    eWeakenInsert = localNames $ do

      lemma <- idLemmaWeakenInsertEnv hcn
      delta <- freshEnvVar etn
      c     <- freshCutoffVar hntn
      ev1   <- freshEnvVar etn
      ev2   <- freshEnvVar etn

      statement <- TermForall
                   <$> sequence
                       [ toBinder delta
                       , toImplicitBinder c
                       , toImplicitBinder ev1
                       , toImplicitBinder ev2
                       ]
                   <*> (TermFunction
                        <$> toTerm (InsertEnv (CVar c) (EVar ev1) (EVar ev2))
                        <*> toTerm
                            (InsertEnv
                              (CWeaken (CVar c) (HVDomainEnv (EVar delta)))
                              (EAppend (EVar ev1) (EVar delta))
                              (EAppend (EVar ev2) (EShift' (CVar c) (EVar delta)))
                            )
                       )

      return $
        SentenceAssertionProof
          (Assertion AssLemma lemma [] statement)
          (ProofQed [PrTactic "needleGenericWeakenInsertEnv" []])
