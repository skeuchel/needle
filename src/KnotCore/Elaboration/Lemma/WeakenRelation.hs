{-# LANGUAGE GADTs #-}

module KnotCore.Elaboration.Lemma.WeakenRelation where

import Coq.StdLib
import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core
import KnotCore.Elaboration.Eq

import Control.Applicative
import Control.Arrow
import Control.Monad ((>=>))
import Data.Maybe (catMaybes)
import Data.Traversable (for, traverse, sequenceA)

lemmas :: Elab m => [RelationGroupDecl] -> m [Sentence]
lemmas rgds = catMaybes <$> traverse eRelationDecl (concatMap rgRelations rgds)

eRelationDecl :: Elab m => RelationDecl -> m (Maybe Sentence)
eRelationDecl (RelationDecl Nothing _ _ _ _ _) = return Nothing
eRelationDecl (RelationDecl (Just ev) rtn fds _ _ _) = do

  let etn = typeNameOf ev
  evd <- freshEnvVariable etn
  evg <- freshEnvVariable etn
  fds' <- freshen fds
  fs'  <- eFieldDeclFields fds'
  jmv <- freshJudgementVariable rtn
  outFnEtns <- lookupRelationOutputs rtn
  outFnEvs <- for outFnEtns $ \(fn,etn) -> (,) fn <$> freshEnvVariable etn
  let jmt = Judgement rtn
              (Just (SymEnvVar evg))
              (map (fieldDeclToSymbolicField Nil) fds')
              (map (second SymEnvVar) outFnEvs)
  binders <-
    sequenceA
    (toBinder evg :
     eFieldDeclBinders fds' ++
     map (toBinder.snd) outFnEvs ++
     [jvBinder jmv jmt]
    )

  nil       <- getEnvCtorNil etn
  conss     <- getEnvCtorConss etn

  nilEq <-
    Equation
    <$> (PatCtor <$> toQualId nil <*> pure [])
    <*> (TermAbs binders <$> toRef jmv)

  rec <-
    TermApp
      <$> (idLemmaWeakenRelation rtn >>= toRef)
      <*> sequenceA
          ( toRef evd :
            toRef evg :
            eFieldDeclRefs fds' ++
            map (toRef.snd) outFnEvs ++ [toRef jmv]
          )

  consEqs <- for conss $ \cons -> do
    EnvCtorCons cn mv' fds'' _mbRtn <- freshen cons
    fs'' <- eFieldDeclFields fds''
    let ntn = typeNameOf mv'
    Equation
      <$> (PatCtor
           <$> toQualId cn
           <*> sequenceA (toId evd:eFieldDeclIdentifiers fds'')
          )
      <*> (TermAbs binders
           <$> (TermApp
                <$> (idLemmaShiftRelation etn (typeNameOf mv') rtn >>= toRef)
                <*> sequenceA
                    ( toTerm (EAppend (EVar evg) (EVar evd))
                    : map (\f ->
                            toTerm (weakenField
                                      f
                                      (HVDomainEnv (EVar evd)))) fs'
                    ++ map (\(_fn,ev) -> toTerm (EWeaken (EVar ev) (HVDomainEnv (EVar evd)))) outFnEvs
                    ++
                      [ pure rec
                      , toTerm (C0 (typeNameOf mv'))
                      , toTerm (ECons (EAppend (EVar evg) (EVar evd)) ntn fs'')
                      , idCtorInsertEnvHere cn >>= toRef
                      ]
                    )
               )
          )

  result    <-
    TermForall binders
    <$> toTerm (PJudgement rtn
                (JudgementEnvTerm (EAppend (EVar evg) (EVar evd)))
                (map (\f -> weakenField f (HVDomainEnv (EVar evd))) fs')
                (map (\(fn,ev) -> EWeaken (EVar ev) (HVDomainEnv (EVar evd))) outFnEvs)
               )

  body <- FixpointBody
          <$> idLemmaWeakenRelation rtn
          <*> sequenceA [toBinder evd]
          <*> pure Nothing
          <*> pure result
          <*> (TermMatch
               <$> (MatchItem
                    <$> toRef evd
                    <*> pure Nothing
                    <*> pure Nothing
                   )
               <*> pure (Just result)
               <*> pure (nilEq:consEqs)
              )

  return (Just (SentenceFixpoint (Fixpoint [body])))
