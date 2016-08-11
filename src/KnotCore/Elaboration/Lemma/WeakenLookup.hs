{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module KnotCore.Elaboration.Lemma.WeakenLookup where

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
  EnvTypeName ->
  CtorName ->
  NamespaceTypeName ->
  [FieldDecl 'WOMV] -> m Sentence
lemma etn cn ntn fds = localNames $ do

  gamma     <- freshEnvVariable etn
  delta     <- freshEnvVariable etn
  x         <- freshIndexVar ntn
  fds'      <- freshen fds
  fs        <- eFieldDeclFields fds'

  statement <-
    TermForall
    <$> sequenceA
        ( toImplicitBinder gamma
        : toBinder delta
        : toImplicitBinder x
        : eFieldDeclBinders fds'
        )
    <*> (TermFunction
         <$> toTerm (Lookup (EVar gamma) (IVar x) fs)
         <*> toTerm
             (Lookup (EAppend (EVar gamma) (EVar delta))
              (IWeaken (IVar x) (HVDomainEnv (EVar delta)))
              (map (flip weakenField (HVDomainEnv (EVar delta))) fs)
             )
        )

  lemma <- idLemmaWeakenLookup cn

  return $
    SentenceAssertionProof
      (Assertion AssLemma lemma [] statement)
      (ProofQed [PrTactic "needleGenericWeakenLookup" []])
