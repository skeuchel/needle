{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module KnotCore.Elaboration.Lemma.DomainOutput where

import Coq.StdLib
import Coq.Syntax

import KnotCore.Syntax
import KnotCore.DeBruijn.Core
import KnotCore.DeBruijn.Eq
import KnotCore.Elaboration.Core
import KnotCore.Elaboration.Eq

import Control.Applicative
import Control.Arrow
import Control.Monad.Error.Class
import Data.Maybe (catMaybes)
import Data.Traversable (for, traverse, sequenceA)

--------------------------------------------------------------------------------

lemmas :: Elab m => [RelationGroupDecl] -> m [Sentence]
lemmas rgds = concat <$> traverse eRelationGroupDecl rgds

eRelationGroupDecl :: Elab m => RelationGroupDecl -> m [Sentence]
eRelationGroupDecl (RelationGroupDecl (Just _etn) rds) = do
  bodiess <- for rds $ \rd -> localNames $ do
    RelationDecl (Just ev) rtn fds _roots outputs rules <- freshen rd
    outFnEvs <- for outputs $ \(fn,etn) -> (,) fn <$> freshEnvVariable etn
    for outFnEvs $ \outFnEv ->
      eRelationDecl rtn ev fds outFnEvs outFnEv rules
  case concat bodiess of
    []     -> pure []
    bodies -> pure [SentenceFixpoint (Fixpoint bodies)]

eRelationGroupDecl (RelationGroupDecl Nothing _) = pure []

eRelationDecl :: Elab m => RelationTypeName -> EnvVariable -> [FieldDecl 'WOMV] ->
  [(FunName,EnvVariable)] -> (FunName,EnvVariable) -> [Rule] -> m FixpointBody
eRelationDecl rtn ev fds outFnEvs (outFn,outEv) rules = localNames $ do

  fds' <- freshen fds
  fs   <- eFieldDeclFields fds'
  jmv  <- freshJudgementVariable rtn
  let jmt = Judgement rtn
              (Just (SymEnvVar ev))
              (map (fieldDeclToSymbolicField Nil) fds')
              (map (second SymEnvVar) outFnEvs)
  st1 <- case fds' of
           FieldDeclSort _ sv _:_ -> pure (SVar sv)
           _ -> error "DomainOutput"

  let result = PEqHvl (HVDomainEnv (EVar outEv)) (HVCall outFn st1)

  equations <- for rules $ \rule ->
     runElabRuleT
       (eRule ev outFn rule)
       (makeElabRuleEnv (rulePremises rule))

  FixpointBody
    <$> idLemmaDomainOutput rtn outFn
    <*> sequenceA
          (toBinder ev :
           eFieldDeclBinders fds' ++
           map (toBinder.snd) outFnEvs ++
           [jvBinder jmv jmt]
          )
    <*> pure Nothing
    <*> toTerm result
    <*> (TermMatch
         <$> (MatchItem
              <$> toRef jmv
              <*> pure Nothing
              <*> (Just
                   <$> toTerm
                       (PJudgement rtn
                          JudgementEnvUnderscore
                          fs
                          (map (EVar . snd) outFnEvs)
                       )
                  )
             )
         <*> (Just <$> toTerm result)
         <*> pure equations
        )


eRule :: ElabRuleM m => EnvVariable -> FunName -> Rule -> m Equation
eRule ev fn (RuleReg cn rmbs premises (Judgement _rtn _mbSe _sts _outFnSes) outFnRbs) = do


  wfs   <- catMaybes <$> traverse (eRuleMetavarWellFormed (Just ev)) rmbs

  ids1  <- catMaybes <$> traverse eRuleMetavarId rmbs
  ids2  <- traverse eFormulaId premises
  ids3  <- traverse (toId . snd) wfs

  fnRbs <- case lookup fn outFnRbs of
             Just fnRbs -> pure fnRbs
             Nothing ->
               throwError "KnotCore.Elaboration.Lemma.DomainOutput: IMPOSSIBLE"

  Equation
    <$> (PatCtorEx
         <$> toQualId cn
         <*> (pure . concat $
              [ -- The environment parameter is replaced in the match
                [] -- [PatUnderscore]
              , map
                  (PatQualId . Ident)
                  (ids1 ++ ids2 ++ ids3)
              ])
        )
    <*> (eqhvlRuleBindSpecDomain (typeNameOf ev) fnRbs >>= toTerm)
