{-# LANGUAGE DataKinds #-}

module KnotCore.Elaboration.Relation where

import qualified Coq.StdLib as Coq
import qualified Coq.Syntax as Coq

import           KnotCore.Elaboration.Core

import           Data.Maybe
import           Data.Traversable (Traversable(..))


eRelationType :: Elab m =>
  [FieldDecl 'WOMV] -> [(FunName, EnvTypeName)] -> m Coq.Term
eRelationType fds outputs =
  Coq.prop . concat <$>
    sequenceA
      [ sequenceA (eFieldDeclTypes fds)
      , traverse (toRef . snd) outputs
      ]

eRelationGroupDecl :: Elab m => RelationGroupDecl -> m Coq.Sentence
eRelationGroupDecl (RelationGroupDecl _ rds) =
  Coq.SentenceInductive . Coq.Inductive <$> traverse eRelationDecl rds

eRelationDecl :: Elab m => RelationDecl -> m Coq.InductiveBody
eRelationDecl (RelationDecl mbEv rtn indices _roots outputs rules) =
  Coq.InductiveBody
    <$> toId rtn
    <*> traverse toBinder (maybeToList mbEv)
    <*> eRelationType indices outputs
    <*> traverse (eRule mbEv) rules


eRule :: Elab m => Maybe EnvVariable -> Rule -> m Coq.InductiveCtor
eRule mbEv r = case r of
  RuleVar cn metaBinds etn fv sfs conc
    | Just ev <- mbEv -> do
        lkv <- freshLookupVar (SymEnvVar ev) fv sfs
        binders1  <- catMaybes <$> traverse eRuleMetavarBinder metaBinds
        binders2  <- traverse toBinder [lkv]
        binders3' <- map snd . catMaybes <$> traverse (eRuleMetavarWellFormed mbEv) metaBinds
        binders3  <- traverse toBinder binders3'
        Coq.InductiveCtor
          <$> toId cn
          <*> pure (binders1 ++ binders2 ++ binders3)
          <*> (Just <$> eJudgement conc)

  RuleReg cn metaBinds prem conc _outs -> do
    binders1  <- catMaybes <$> traverse eRuleMetavarBinder metaBinds
    binders2  <- traverse eFormula prem
    binders3' <- map snd . catMaybes <$> traverse (eRuleMetavarWellFormed mbEv) metaBinds
    binders3  <- traverse toBinder binders3'

    Coq.InductiveCtor
      <$> toId cn
      <*> pure (binders1 ++ binders2 ++ binders3)
      <*> (Just <$> eJudgement conc)

eFormula :: Elab m => Formula -> m Coq.Binder
eFormula (FormJudgement jmv _ jmt _) = jvBinder jmv jmt
eFormula (FormLookup lkv _ _ _)      = toBinder lkv

eJudgement :: Elab m => Judgement -> m Coq.Term
eJudgement (Judgement rtn mbEnv sfs outs) = do
  fs <- catMaybes <$> traverse symbolicFieldToField sfs
  Coq.TermApp
    <$> toRef rtn
    <*> (concat <$> sequenceA
         [ traverse eSymbolicEnv (maybeToList mbEnv)
         , traverse toTerm fs
         , traverse (eSymbolicEnv . snd) outs
         ]
        )
