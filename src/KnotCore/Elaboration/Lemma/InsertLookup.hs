{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module KnotCore.Elaboration.Lemma.InsertLookup where

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
  [ lemma etn (typeNameOf insMv) (typeNameOf lkMv) lkFields
  | EnvCtorCons _ insMv _ _mbInsRtn <- ecs
  , EnvCtorCons _ lkMv lkFields _mvLkRtn <- ecs
  ]

lemma :: Elab m =>
  EnvTypeName -> NamespaceTypeName ->
  NamespaceTypeName -> [FieldDecl 'WOMV] -> m Sentence
lemma etn insNtn lkNtn lkFields = localNames $ do

  co        <- freshCutoffVar insNtn
  en1       <- freshEnvVariable etn
  en2       <- freshEnvVariable etn
  insertC   <- toTerm (InsertEnv (CVar co) (EVar en1) (EVar en2))
  premise   <- freshVariable "ins" insertC

  x         <- freshIndexVar lkNtn
  lkFields' <- freshen lkFields
  ts        <- eFieldDeclFields lkFields'

  statement <-
    TermForall
    <$> sequenceA
        ( toImplicitBinder co
        : toImplicitBinder en1
        : toImplicitBinder en2
        : toBinder premise
        : toImplicitBinder x
        : eFieldDeclImplicitBinders lkFields'
        )
    <*> (TermFunction
         <$> toTerm (Lookup (EVar en1) (IVar x) ts)
         <*> toTerm
             (Lookup (EVar en2)
              (IShift' (CVar co) (IVar x))
              (map (shiftField (CVar co)) ts)
             )
        )

  lemma <- idLemmaInsertLookup etn insNtn lkNtn

  return $
    SentenceAssertionProof
      (Assertion AssLemma lemma [] statement)
      (ProofQed [PrTactic "needleGenericInsertLookup" []])
