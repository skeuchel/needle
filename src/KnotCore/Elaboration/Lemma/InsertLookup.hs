
module KnotCore.Elaboration.Lemma.InsertLookup where

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
  [ lemma etn (typeNameOf insMv) (typeNameOf lkMv) lkFields
  | EnvCtorCons _ insMv _ <- ecs
  , EnvCtorCons _ lkMv lkFields <- ecs
  ]

lemma :: Elab m =>
  EnvTypeName -> NamespaceTypeName ->
  NamespaceTypeName -> [SubtreeVar] -> m Sentence
lemma etn insNtn lkNtn lkFields = localNames $ do

  co        <- freshCutoffVar insNtn
  en1       <- freshEnvVar etn
  en2       <- freshEnvVar etn
  insertC   <- toTerm (InsertEnv (CVar co) (EVar en1) (EVar en2))
  premise   <- freshVariable "ins" insertC

  x         <- freshIndexVar lkNtn
  ts        <- mapM freshen lkFields

  statement <-
    TermForall
    <$> sequence
        ( toImplicitBinder co
        : toImplicitBinder en1
        : toImplicitBinder en2
        : toBinder premise
        : toImplicitBinder x
        : map toImplicitBinder ts
        )
    <*> (TermFunction
         <$> toTerm (Lookup (EVar en1) (IVar x) (map SVar ts))
         <*> toTerm
             (Lookup (EVar en2)
              (IShift' (CVar co) (IVar x))
              [SShift' (CVar co) (SVar t) | t <- ts]
             )
        )

  lemma <- idLemmaInsertLookup etn insNtn lkNtn

  return $
    SentenceAssertionProof
      (Assertion AssLemma lemma [] statement)
      (ProofQed [PrTactic "needleGenericInsertLookup" []])
