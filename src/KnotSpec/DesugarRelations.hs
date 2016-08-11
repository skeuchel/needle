{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}

module KnotSpec.DesugarRelations where

import           Knot.Env
import           Knot.Fresh
import           KnotSpec.Syntax hiding (envCtorName)
import           KnotSpec.DesugarSorts

import qualified KnotCore.Syntax as Core
import qualified KnotCore.Environment as Core
import qualified KnotCore.Elaboration.Fresh as Core

import           Control.Arrow
import           Control.Monad.Error.Class
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.Reader (ReaderT, runReaderT)
import           Data.Foldable
import qualified Data.Foldable as F
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Maybe

--------------------------------------------------------------------------------

relationGroupDecl :: DesugarM m =>
  RelationGroupDecl 'Grouped -> m Core.RelationGroupDecl
relationGroupDecl (RelationGroupDecl rds) =
  Core.RelationGroupDecl
    (msum [ mbEtn | RelationDecl mbEtn _ _ _ _ _ <- rds ])
    <$> traverse relationDecl rds

relationDecl :: DesugarM m => RelationDecl 'Grouped -> m Core.RelationDecl
relationDecl (RelationDecl mbEtn rtn fields nrs outputs rules) = localNames $ do
  mbEv <- traverse freshEnvVariable mbEtn
  Core.RelationDecl mbEv rtn
    <$> traverse fieldDecl fields
    <*> pure nrs
    <*> pure outputs
    <*> traverse (desugarRule mbEv) rules

--------------------------------------------------------------------------------

class (Applicative m, MonadError String m, EnvM m, FreshM m) => DesugarRelM m where
  lookupBindingBindSpec  :: BindingVariable -> m (BindSpec 'Grouped)
  lookupJudgement        :: JudgementVariable -> m (RuleBindSpec 'Grouped, Judgement 'Grouped)
  lookupJudgementOutput  :: FunName -> JudgementVariable -> m EnvVariable

desugarRule :: (MonadError String m, EnvM m, FreshM m) =>
  Maybe EnvVariable -> Rule 'Grouped -> m Core.Rule
desugarRule mbEv r = case r of
  RuleVar cn rmbs etn fv sfs jm ->
    runDesugarRelT
      (do
         Core.RuleVar cn
           <$> traverse (ruleMetavarBinder M.empty) rmbs
           <*> pure etn <*> pure fv
           <*> traverse symbolicField sfs
           <*> judgement (Core.SymEnvVar <$> mbEv) jm []
      )
      (makeDesugarRelEnv rmbs [])

  RuleReg cn rmbs premises conclusion rbss ->
    runDesugarRelT
      (do
         premises' <- traverse (formula mbEv) premises
         let meSvPos = Core.mkMESortVariablePos premises'
         outputs' <- traverse (\(fn,rbs) -> (,) fn <$> evalRuleBindSpec (Core.SymEnvNil (typeNameOf (fromJust mbEv))) rbs) rbss
         Core.RuleReg cn
           <$> ((++)
                  <$> traverse (ruleMetavarBinder meSvPos) rmbs
                  <*> sequenceA
                        [ flip Core.RuleMetavarOutput ev <$> ruleBindSpec (fmlJmtRuleBindSpec jmt)
                        | jmt@FormJudgement{} <- premises, (_,ev) <- fmtJmtOutputs jmt
                        ]
               )
           <*> pure premises'
           <*> judgement (Core.SymEnvVar <$> mbEv) conclusion outputs'
           <*> traverse (\(fn,rbs) -> (,) fn <$> ruleBindSpec rbs) rbss
      )
      (makeDesugarRelEnv rmbs premises)

--------------------------------------------------------------------------------

evalRuleBindSpecItem :: DesugarRelM m =>
  Core.SymbolicEnv -> RuleBindSpecItem 'Grouped -> m Core.SymbolicEnv
evalRuleBindSpecItem se rbsi = case rbsi of
  RuleBsiBinding bv sfs ->
    Core.SymEnvCons (bvNtn bv) se <$> traverse symbolicField sfs
  RuleBsiCall fn jmv -> do
    ev <- lookupJudgementOutput fn jmv
    pure (Core.SymEnvAppend se (Core.SymEnvVar ev))

evalRuleBindSpec :: DesugarRelM m =>
  Core.SymbolicEnv -> RuleBindSpec 'Grouped -> m Core.SymbolicEnv
evalRuleBindSpec se rbs' = case rbs' of
  Nil         -> pure se
  rbs :. rbsi -> do
    se' <- evalRuleBindSpec se rbs
    evalRuleBindSpecItem se' rbsi

--------------------------------------------------------------------------------

ruleMetavarBinder :: DesugarRelM m => Core.MESortVariablePos ->
  RuleMetavarBinder 'Grouped -> m Core.RuleMetavarBinder
ruleMetavarBinder mSvPos rmb = case rmb of
  RuleMetavarSort bs sv    -> Core.RuleMetavarSort
                                <$> bindSpec bs
                                <*> pure sv
                                <*> Core.freshHypothesis
                                <*> pure (M.lookup sv mSvPos)
  RuleMetavarFree fv       -> Core.RuleMetavarFree
                                <$> pure fv
                                <*> Core.freshHypothesis
  RuleMetavarBinding bs bv -> Core.RuleMetavarBinding
                                <$> bindSpec bs
                                <*> pure bv


formula :: DesugarRelM m => Maybe EnvVariable ->
  Formula 'Grouped -> m Core.Formula
formula (Just ev) (FormLookup _ fv sfs) = do
  sfs' <- traverse symbolicField sfs
  lkv <- Core.freshLookupVar (Core.SymEnvVar ev) fv sfs'
  return (Core.FormLookup lkv ev fv sfs')
formula Nothing (FormLookup{}) =
  error "ERROR: KnotSpec.Desugar.formula"
formula mbEv (FormJudgement jmv rbs jmt outs) = do
  mbSe <- traverse (\ev -> Core.SymEnvAppend (Core.SymEnvVar ev) <$> evalRuleBindSpec (Core.SymEnvNil (typeNameOf ev)) rbs) mbEv
  jm' <- judgement mbSe jmt (map (second Core.SymEnvVar) outs)
  Core.FormJudgement jmv
    <$> ruleBindSpec rbs
    <*> pure jm'
    <*> pure outs

ruleBindSpec :: DesugarRelM m => RuleBindSpec 'Grouped -> m Core.RuleBindSpec
ruleBindSpec = traverse ruleBindSpecItem

ruleBindSpecItem :: DesugarRelM m =>
  RuleBindSpecItem 'Grouped -> m Core.RuleBindSpecItem
ruleBindSpecItem rbsi = case rbsi of
  RuleBsiBinding bv sfs ->
    Core.RuleBsiBinding bv <$> traverse symbolicField sfs
  RuleBsiCall fn jv -> pure (Core.RuleBsiCall fn jv)

judgement :: DesugarRelM m => Maybe Core.SymbolicEnv ->
  Judgement 'Grouped -> [(FunName, Core.SymbolicEnv)] -> m Core.Judgement
judgement mbSe (Judgement rtn _mbEtn sfs) outs =
  Core.Judgement rtn mbSe
    <$> traverse symbolicField sfs
    <*> pure outs

--------------------------------------------------------------------------------

symbolicTerm :: DesugarRelM m => SymbolicTerm 'Grouped -> m Core.SymbolicTerm
symbolicTerm (SymVar scp sv)
  = Core.SymSubtree
    <$> bindSpec scp
    <*> pure sv
symbolicTerm (SymCtorVarFree scp cn fv)
  = Core.SymCtorVarFree
    <$> bindSpec scp
    <*> pure cn
    <*> pure fv
symbolicTerm (SymCtorVarBound scp cn bv) = do
  bvBs <- lookupBindingBindSpec bv
  Core.SymCtorVarBound
    <$> bindSpec scp
    <*> pure cn
    <*> pure bv
    <*> bindSpec bvBs
    <*> (dropPrefix (bvBs :. BsiBinding bv) scp >>= bindSpec)
symbolicTerm (SymCtorReg scp cn sfs)
  = Core.SymCtorReg
    <$> bindSpec scp
    <*> pure cn
    <*> traverse symbolicField sfs
symbolicTerm (SymWeaken scp inScp st bs) =
  Core.SymWeaken
    <$> bindSpec scp
    <*> bindSpec inScp
    <*> symbolicTerm st
    <*> bindSpec bs
symbolicTerm (SymSubst scp bv st1 st2) =
  Core.SymSubst
    <$> bindSpec scp
    <*> pure bv
    <*> symbolicTerm st1
    <*> symbolicTerm st2

symbolicEnv :: DesugarRelM m => SymbolicEnv 'Grouped -> m Core.SymbolicEnv
symbolicEnv se' = case se' of
  SymEnvVar _bs ev -> pure (Core.SymEnvVar ev)   -- TODO: Desugar bs
  SymEnvNil _bs etn -> pure (Core.SymEnvNil etn) -- TODO: Desugar bs
  SymEnvCons _bs se _cn ntn sfs ->               -- TODO: Desugar bs
    Core.SymEnvCons ntn <$> symbolicEnv se <*> traverse symbolicField sfs

symbolicField :: DesugarRelM m =>
  SymbolicField w 'Grouped -> m (Core.SymbolicField w)
symbolicField sf' = case sf' of
  SymFieldSort _loc scp st ->
    Core.SymFieldSort <$> bindSpec scp <*> pure Nil <*> symbolicTerm st
  SymFieldEnv _loc scp se ->
    Core.SymFieldEnv <$> bindSpec scp <*> pure Nil <*> symbolicEnv se
  SymFieldBinding _loc bs bv ->
    Core.SymFieldBinding <$> bindSpec bs <*> pure bv
  SymFieldReferenceFree _loc bs fv ->
    Core.SymFieldReferenceFree <$> bindSpec bs <*> pure fv
  SymFieldReferenceBound _loc bs bv ->
    Core.SymFieldReferenceBound <$> bindSpec bs <*> pure bv

--------------------------------------------------------------------------------

data DesugarRelEnv =
  DesugarRelEnv
  { envBindingBindSpec :: Map BindingVariable (BindSpec 'Grouped)
  , envJudgement  :: Map JudgementVariable (RuleBindSpec 'Grouped, Judgement 'Grouped)
  , envJudgementOutput :: Map (FunName, JudgementVariable) EnvVariable
  }
  deriving Show

makeDesugarRelEnv :: [RuleMetavarBinder 'Grouped] -> [Formula 'Grouped] -> DesugarRelEnv
makeDesugarRelEnv rmbs fmls =
  DesugarRelEnv
    (M.fromList [ (bv,bs)  | RuleMetavarBinding bs bv <- rmbs ])
    (M.fromList [ (jv,(rbs,jmt)) | FormJudgement jv rbs jmt _outs <- fmls ])
    (M.fromList
       [ ((fn,jv),ev)
       | FormJudgement jv _rbs _jmt outs <- fmls
       , (fn,ev) <- outs
       ])

newtype DesugarRelT m a = DesugarRelT { fromDesugarRelT :: ReaderT DesugarRelEnv m a }
  deriving (Functor, Applicative, Monad, MonadError e, MonadTrans, EnvM, FreshM)

instance (MonadError String m, EnvM m, FreshM m) => DesugarRelM (DesugarRelT m) where
  lookupBindingBindSpec bv = DesugarRelT $ lookupEnv bv envBindingBindSpec
    "KnotSpec.DesugarRelations.DesugarRelM(DesugarRelT).lookupBindingBindSpec"
  lookupJudgement jv = DesugarRelT $ lookupEnv jv envJudgement
    "KnotSpec.DesugarRelations.DesugarRelM(DesugarRelT).lookupJudgement"
  lookupJudgementOutput fn jv = DesugarRelT $ lookupEnv (fn,jv) envJudgementOutput
    "KnotSpec.DesugarRelations.DesugarRelM(DesugarRelT).lookupJudgementOutput"

runDesugarRelT :: DesugarRelT m a -> DesugarRelEnv -> m a
runDesugarRelT = runReaderT . fromDesugarRelT
