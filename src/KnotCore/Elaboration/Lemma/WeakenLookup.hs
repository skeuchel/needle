
module KnotCore.Elaboration.Lemma.WeakenLookup where

import Control.Applicative
import Control.Monad

import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core

lemmass :: Elab m => [EnvDecl] -> m [Sentence]
lemmass = fmap concat . mapM lemmas

lemmas :: Elab m => EnvDecl -> m [Sentence]
lemmas (EnvDecl etn _ ecs) =
  sequence
  [ lemma etn cn (typeNameOf mv) fields
  | EnvCtorCons cn mv fields <- ecs
  ]

lemma :: Elab m =>
  EnvTypeName ->
  CtorName ->
  NamespaceTypeName ->
  [SubtreeVar] -> m Sentence
lemma etn cn ntn fields = localNames $ do

  gamma     <- freshEnvVar etn
  delta     <- freshEnvVar etn
  x         <- freshIndexVar ntn
  ts        <- mapM freshen fields

  statement <-
    TermForall
    <$> sequence
        ( toImplicitBinder gamma
        : toBinder delta
        : toImplicitBinder x
        : map toImplicitBinder ts
        )
    <*> (TermFunction
         <$> toTerm (Lookup (EVar gamma) (IVar x) (map SVar ts))
         <*> toTerm
             (Lookup (EAppend (EVar gamma) (EVar delta))
              (IWeaken (IVar x) (HVDomainEnv (EVar delta)))
              [SWeaken (SVar t) (HVDomainEnv (EVar delta)) | t <- ts]
             )
        )

  lemma <- idLemmaWeakenLookup cn

  return $
    SentenceAssertionProof
      (Assertion AssLemma lemma [] statement)
      (ProofQed [PrTactic "needleGenericWeakenLookup" []])
