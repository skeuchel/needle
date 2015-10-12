
module KnotCore.Elaboration.Lemma.WeakenLookupHere where

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

  stn       <- getSortOfNamespace ntn
  gamma     <- freshEnvVar etn
  delta     <- freshEnvVar etn
  ts        <- mapM freshen fields
  binders   <- forM ts $ \sv ->
                 sequence
                 [ toImplicitBinder sv
                 , toTerm (WfTerm (HVDomainEnv (EVar gamma)) (SVar sv)) >>=
                   freshVariable "wf" >>= toBinder
                 ]

  statement <-
    TermForall
    <$> sequence
        ( toImplicitBinder gamma
        : toBinder delta
        : map pure (concat binders)
        )
    <*> toTerm
          (Lookup
            (EAppend
              (ECtor cn (EVar gamma) (map SVar ts))
              (EVar delta)
            )
            (IWeaken (I0 ntn stn) (HVDomainEnv (EVar delta)))
            (map (\sv -> SWeaken (SShift' (C0 ntn) (SVar sv)) (HVDomainEnv (EVar delta))) ts)
          )

  lemma <- idLemmaWeakenLookupHere cn

  return $
    SentenceAssertionProof
      (Assertion AssLemma lemma [] statement)
      (ProofQed [PrTactic "eauto with lookup" []])
