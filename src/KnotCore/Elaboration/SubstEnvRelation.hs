{-# LANGUAGE ScopedTypeVariables #-}

module KnotCore.Elaboration.SubstEnvRelation where

import Control.Applicative
import Data.Maybe

import Coq.StdLib
import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core

eSubstEnvRelationss :: Elab m => [EnvDecl] -> m [Sentence]
eSubstEnvRelationss = fmap concat . mapM eSubstEnvRelations

eSubstEnvRelations :: Elab m => EnvDecl -> m [Sentence]
eSubstEnvRelations (EnvDecl etn _ ecs) =
  concat <$> sequence
    [ localNames $ do
        henv     <- freshEnvVar etn
        (stn,_)  <- getNamespaceCtor hntn
        ht       <- freshSubtreeVar stn
        hfields' <- freshen hfields

        eSubstEnvRelation henv hcn hntn hfields' ht ecs
    | EnvCtorCons hcn hmv hfields <- ecs
    , let hntn = typeNameOf hmv
    ]

eSubstEnvRelation ::
  forall m. Elab m =>
  EnvVar ->
  CtorName -> NamespaceTypeName -> [SubtreeVar] -> SubtreeVar ->
  [EnvCtor] -> m [Sentence]
eSubstEnvRelation henv hcn hntn hfields ht ecs = sequence [ eDeclaration, eWeakenSubstEnv ]
  where
    etn :: EnvTypeName
    etn = typeNameOf henv

    eDeclaration :: m Sentence
    eDeclaration = do
      body <-
        InductiveBody
          <$> idTypeSubstEnv hcn
          <*> sequence
              ([toBinder henv] ++
               map toBinder hfields ++
               [toBinder ht]
              )
          <*> (prop
               <$> sequence
                   [ typeTrace hntn
                   , toRef etn
                   , toRef etn
                   ]
               )
          <*> sequence
              (eSubstEnvHere:
               [ eSubstEnvThere tcn tntn tfields
               | EnvCtorCons tcn tmv tfields <- ecs
               , let tntn = typeNameOf tmv
               ]
              )

      return $ SentenceInductive (Inductive [body])

    eSubstEnvHere :: m InductiveCtor
    eSubstEnvHere = localNames $ do

      InductiveCtor
        <$> idCtorSubstEnvHere hcn
        <*> pure []
        <*> (Just
             <$> toTerm (SubstEnv
                          (EVar henv)
                          (map SVar hfields)
                          (SVar ht)
                          (T0 hntn)
                          (ECtor hcn (EVar henv) (map SVar hfields))
                          (EVar henv)
                        )
            )

    eSubstEnvThere :: CtorName -> NamespaceTypeName -> [SubtreeVar] -> m InductiveCtor
    eSubstEnvThere tcn tntn tfields = localNames $ do

      x       <- freshTraceVar hntn
      ev1     <- freshEnvVar etn
      ev2     <- freshEnvVar etn

      premise <- toTerm
                 (SubstEnv
                    (EVar henv)
                    (map SVar hfields)
                    (SVar ht)
                    (TVar x)
                    (EVar ev1)
                    (EVar ev2)
                 )
      concl   <- toTerm
                 (SubstEnv
                    (EVar henv)
                    (map SVar hfields)
                    (SVar ht)
                    (TS tntn (TVar x))
                    (ECtor tcn (EVar ev1) (map SVar tfields))
                    (ECtor tcn (EVar ev2) (map (SSubst' (TVar x) (SVar ht) . SVar) tfields))
                 )

      InductiveCtor
        <$> idCtorSubstEnvThere hcn tcn
        <*> sequence (toImplicitBinder x:
                      toImplicitBinder ev1:
                      toImplicitBinder ev2:
                      map toImplicitBinder tfields)
        <*> pure (Just $ TermFunction premise concl)

    eWeakenSubstEnv :: m Sentence
    eWeakenSubstEnv = localNames $ do

      lemma <- idLemmaWeakenSubstEnv hcn
      delta <- freshEnvVar etn
      x     <- freshTraceVar hntn
      ev1   <- freshEnvVar etn
      ev2   <- freshEnvVar etn

      binders   <- sequence
                   ([ toImplicitBinder henv ] ++
                    map toImplicitBinder hfields ++
                    [ toImplicitBinder ht ]
                   )

      statement <- TermForall
                   <$> sequence
                       [ toBinder delta
                       , toImplicitBinder x
                       , toImplicitBinder ev1
                       , toImplicitBinder ev2
                       ]
                   <*> (TermFunction
                        <$> toTerm
                            (SubstEnv
                              (EVar henv)
                              (map SVar hfields)
                              (SVar ht)
                              (TVar x)
                              (EVar ev1)
                              (EVar ev2))
                        <*> toTerm
                            (SubstEnv
                              (EVar henv)
                              (map SVar hfields)
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
