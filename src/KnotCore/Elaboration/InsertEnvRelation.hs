{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module KnotCore.Elaboration.InsertEnvRelation where

import Control.Applicative
import Data.Maybe

import Coq.StdLib
import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core

eInsertEnvRelationss :: Elab m => [EnvDecl] -> m [Sentence]
eInsertEnvRelationss = fmap concat . traverse eInsertEnvRelations

eInsertEnvRelations :: Elab m => EnvDecl -> m [Sentence]
eInsertEnvRelations (EnvDecl etn _ ecs) =
  concat <$> sequenceA
    [ localNames $ do
        hfields' <- freshen hfields
        eInsertEnvRelation etn hcn hntn hfields' ecs
    | EnvCtorCons hcn hmv hfields _mbRtn <- ecs
    , let hntn = typeNameOf hmv
    ]

eInsertEnvRelation ::
  forall m. Elab m =>
  EnvTypeName ->
  CtorName -> NamespaceTypeName -> [FieldDecl 'WOMV] ->
  [EnvCtor] -> m [Sentence]
eInsertEnvRelation etn hcn hntn hfields ecs = sequenceA [ eDeclaration, eWeakenInsert ]
  where
    eDeclaration :: m Sentence
    eDeclaration = do
      body <-
        InductiveBody
          <$> idTypeInsertEnv hcn
          <*> pure []
          <*> (prop <$> sequenceA [typeCutoff hntn, toRef etn, toRef etn])
          <*> sequenceA
              (eInsertEnvHere:
               [ eInsertEnvThere tcn tntn tfields
               | EnvCtorCons tcn tmv tfields _mbRtn <- ecs
               , let tntn = typeNameOf tmv
               ]
              )

      return $ SentenceInductive (Inductive [body])

    eInsertEnvHere :: m InductiveCtor
    eInsertEnvHere = localNames $ do

      ev     <- freshEnvVariable etn
      hfs <- eFieldDeclFields hfields

      InductiveCtor
        <$> idCtorInsertEnvHere hcn
        <*> sequenceA (toImplicitBinder ev:eFieldDeclImplicitBinders hfields)
        <*> (Just
             <$> toTerm (InsertEnv
                          (C0 hntn)
                          (EVar ev)
                          (ECons (EVar ev) hntn hfs)
                        )
            )

    eInsertEnvThere :: CtorName -> NamespaceTypeName -> [FieldDecl 'WOMV] -> m InductiveCtor
    eInsertEnvThere tcn tntn tfields = localNames $ do

      c       <- freshCutoffVar hntn
      ev1     <- freshEnvVariable etn
      ev2     <- freshEnvVariable etn
      tfs     <- eFieldDeclFields tfields

      premise <- toTerm (InsertEnv (CVar c) (EVar ev1) (EVar ev2))
      concl   <- toTerm (InsertEnv
                           (CS' tntn (CVar c))
                           (ECons (EVar ev1) tntn tfs)
                           (ECons (EVar ev2) tntn (map (shiftField (CVar c)) tfs)))

      InductiveCtor
        <$> idCtorInsertEnvThere hcn tcn
        <*> sequenceA
            ( toImplicitBinder c:
              toImplicitBinder ev1:
              toImplicitBinder ev2:
              eFieldDeclImplicitBinders tfields
            )
        <*> pure (Just $ TermFunction premise concl)


    eWeakenInsert :: m Sentence
    eWeakenInsert = localNames $ do

      lemma <- idLemmaWeakenInsertEnv hcn
      delta <- freshEnvVariable etn
      c     <- freshCutoffVar hntn
      ev1   <- freshEnvVariable etn
      ev2   <- freshEnvVariable etn

      statement <- TermForall
                   <$> sequenceA
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
