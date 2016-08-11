{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module KnotCore.Elaboration.Lemma.WeakenLookupHere where

import Control.Applicative
import Control.Monad

import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core

lemmass :: Elab m => [EnvDecl] -> m [Sentence]
lemmass = fmap concat . traverse lemmas

lemmas :: Elab m => EnvDecl -> m [Sentence]
lemmas (EnvDecl etn _ ecs) =
  sequenceA
  [ lemma etn cn (typeNameOf mv) fds
  | EnvCtorCons cn mv fds _mbRtn <- ecs
  ]

lemma :: Elab m =>
  EnvTypeName -> CtorName -> NamespaceTypeName ->
  [FieldDecl 'WOMV] -> m Sentence
lemma etn cn ntn fds = localNames $ do

  stn       <- getSortOfNamespace ntn
  gamma     <- freshEnvVariable etn
  delta     <- freshEnvVariable etn
  fds'      <- freshen fds
  fs        <- eFieldDeclFields fds'

  binderss  <- for fds' $ \fd -> case fd of
                 FieldDeclSort _ sv _svWf ->
                   -- TODO: reuse svWf
                   sequenceA
                     [ toImplicitBinder sv
                     , toTerm (WfSort (HVDomainEnv (EVar gamma)) (SVar sv)) >>=
                       freshVariable "wf" >>= toBinder
                     ]

  statement <-
    TermForall
    <$> sequenceA
        ( toImplicitBinder gamma
        : toBinder delta
        : map pure (concat binderss)
        )
    <*> toTerm
          (Lookup
            (EAppend
              (ECons (EVar gamma) ntn fs)
              (EVar delta)
            )
            (IWeaken (I0 ntn stn) (HVDomainEnv (EVar delta)))
            (map (\f -> weakenField (shiftField (C0 ntn) f) (HVDomainEnv (EVar delta))) fs)
          )

  lemma <- idLemmaWeakenLookupHere cn

  return $
    SentenceAssertionProof
      (Assertion AssLemma lemma [] statement)
      (ProofQed [PrTactic "eauto with lookup" []])
