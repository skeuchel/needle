{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}

module KnotSpec.CheckRelations where

import           Knot.Env
import           KnotSpec.CheckSorts
import           KnotSpec.Evaluation
import           KnotSpec.Inference
import           KnotSpec.Substitution
import           KnotSpec.Syntax

import           Control.Monad
import           Control.Monad.Error.Class
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.Reader (ReaderT, runReaderT)
import           Control.Monad.Trans.State.Strict (StateT)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Foldable
import           Data.Traversable

--------------------------------------------------------------------------------

class (TcM m, EvalM m) => RelTcM m where
  lookupConstructorFields :: CtorName ->
    m ([FieldDecl 'WMV 'Checked 'Checked], SortTypeName)
  lookupEnvClauseFields :: EnvTypeName -> NamespaceTypeName ->
    m (BindingVariable, [FieldDecl 'WOMV 'Checked 'Checked])
  lookupRelationFields :: RelationTypeName ->
    m (Maybe EnvTypeName, [FieldDecl 'WOMV 'Checked 'Checked])
instance RelTcM m => RelTcM (StateT s m) where
  lookupConstructorFields = lift . lookupConstructorFields
  lookupEnvClauseFields = (lift.) . lookupEnvClauseFields
  lookupRelationFields = lift . lookupRelationFields
deriving instance RelTcM m => RelTcM (InfT m)

--------------------------------------------------------------------------------

stripBs :: (Applicative m, MonadError String m) =>
  BindSpec 'Checked -> BindSpec 'ResolvedVars -> m (BindSpec 'Checked)
stripBs bs'                      Nil                   = pure bs'
stripBs (bs' :. BsiBinding bv')  (bs :. BsiBinding bv)
  | bv' == bv = stripBs bs' bs
stripBs (bs' :. BsiCall fn' sv') (bs :. BsiCall fn sv)
  | fn' == fn && sv' == sv = stripBs bs' bs
stripBs _ _ = throwError "KnotSpec.CheckRelations.stripBs"

checkSymbolicTerm :: (InfM m, RelTcM m) =>
  BindSpec 'Checked -> SymbolicTerm 'ResolvedVars -> m (SymbolicTerm 'Checked)
checkSymbolicTerm outer _st = case _st of
  SymVar () sv -> do
    checkSubtreeBindSpec sv outer
    pure $! SymVar outer sv
  SymCtorVarFree () cn fv ->
    pure $! SymCtorVarFree outer cn fv
  SymCtorVarBound () cn bv ->
    -- TODO: This should check that bv's scope is a superscope of
    -- outer. however, the real scope of bv might not be known yet at this
    -- point.
    pure $! SymCtorVarBound outer cn bv
  SymCtorReg () cn sfs -> do
    (fds,_stn)  <- lookupConstructorFields cn
    sub <- makeFieldSubstitution fds sfs
    SymCtorReg outer cn <$> zipWithM (checkSymbolicField outer sub) fds sfs
  SymWeaken () () st bs -> do
    inner <- stripBs outer bs
    _bs <- infBindSpec inner bs
    SymWeaken outer inner
      <$> checkSymbolicTerm inner st
      <*> dropPrefix inner outer
  SymSubst () bv st1 st2 -> do
    checkBindingBindSpec bv outer
    SymSubst outer bv
      <$> checkSymbolicTerm outer st1
      <*> checkSymbolicTerm (outer :. BsiBinding bv) st2

checkSymbolicField :: (InfM m, RelTcM m) =>
  BindSpec 'Checked -> Substitution 'ResolvedVars ->
  FieldDecl w 'Checked 'Checked ->
  SymbolicField w 'ResolvedVars -> m (SymbolicField w 'Checked)
checkSymbolicField outer sub fd sf =
  let fun = "KnotSpec.CheckRelations.checkSymbolicField" in case sf of
  SymFieldSort loc () st
    | FieldDeclSort _ bs _ <- fd -> do
        inner <- symEvalBindSpec outer sub bs
        SymFieldSort loc outer <$> checkSymbolicTerm inner st
    | otherwise -> throwError $ fun ++ ".SymFieldSort"
  SymFieldBinding loc () bv
    | FieldDeclBinding _ bs _ <- fd -> do
        inner <- symEvalBindSpec outer sub bs
        checkBindingBindSpec bv inner
        pure (SymFieldBinding loc outer bv)
    | otherwise -> throwError $ fun ++ ".SymFieldBinding"
  SymFieldReferenceBound loc () bv
    | FieldDeclReference _ _ <- fd ->
        -- TODO: This should check that bv's scope is a superscope of
        -- outer. however, the real scope of bv might not be known yet at this
        -- point.
        pure (SymFieldReferenceBound loc outer bv)
    | otherwise -> throwError $ fun ++ ".SymFieldReferenceBound"
  SymFieldReferenceFree loc () rv
    | FieldDeclReference _ _ <- fd ->
        pure (SymFieldReferenceFree loc outer rv)
    | otherwise -> throwError $ fun ++ ".SymFieldReferenceFree"
  SymFieldEnv loc () se
    | FieldDeclEnv _ bs _ <- fd -> do
        inner <- symEvalBindSpec outer sub bs
        SymFieldEnv loc outer <$> checkSymbolicEnv inner se
    | otherwise -> throwError $ fun ++ ".SymFieldEnv"
  SymFieldSet loc () sz
    | FieldDeclSet _ _ <- fd -> do
        SymFieldSet loc outer <$> checkSymbolicSet sz
    | otherwise -> throwError $ fun ++ ".SymFieldSet"

checkSymbolicEnv :: (InfM m, RelTcM m) =>
  BindSpec 'Checked -> SymbolicEnv 'ResolvedVars -> m (SymbolicEnv 'Checked)
checkSymbolicEnv outer _se =
  let fun = "KnotSpec.CheckRelations.checkSymbolicEnv" in case _se of
  SymEnvVar () ev -> do
    checkEnvBindSpec ev outer
    pure $! SymEnvVar outer ev
  SymEnvNil () etn ->
    pure $! SymEnvNil outer etn
  SymEnvCons () _se _cn _ntn _sts ->
    throwError $ fun ++ ".SymEnvCons: NOT IMPLEMENTED"

checkSymbolicSet :: RelTcM m =>
  SymbolicSet 'ResolvedVars -> m (SymbolicSet 'Checked)
checkSymbolicSet sz = case sz of
  SymSetVar zv -> pure (SymSetVar zv)
  SymSetCtor cn szs -> SymSetCtor cn <$> traverse checkSymbolicSet szs

--------------------------------------------------------------------------------

checkRelationDecl :: RelTcM m =>
  RelationDecl 'ResolvedVars -> m (RelationDecl 'Checked)
checkRelationDecl (RelationDecl mbEtn rtn fds nrs outputs rules) = do
  lenv <- flip execInfT defaultInfState $ do
    for_ fds $ \fd -> case fd of
      FieldDeclSort _loc bs sv -> infBindSpec Nil bs >>= checkSubtreeBindSpec sv
      FieldDeclEnv _loc bs ev -> infBindSpec Nil bs >>= checkEnvBindSpec ev
      FieldDeclSet{} -> return ()

  RelationDecl mbEtn rtn
    <$> traverse (checkFieldDecl lenv) fds
    <*> pure nrs
    <*> pure outputs
    <*> traverse (checkRuleDecl mbEtn) rules

checkRuleDecl :: RelTcM m =>
  Maybe EnvTypeName -> Rule 'ResolvedVars -> m (Rule 'Checked)
checkRuleDecl mbEtn r = case r of
  RuleVar cn rmbs etn fv sfs jm -> do

    ((sfs',jm'),lenv) <- flip runInfT defaultInfState $ do
      -- TODO: substitute bv somehow?
      (_bv,fds) <- lookupEnvClauseFields etn (fvNtn fv)
      sub <- makeFieldSubstitution fds sfs
      sfs' <- zipWithM (checkSymbolicField Nil sub) fds sfs
      jm' <- checkJudgement mbEtn Nil jm
      pure (sfs', jm')

    RuleVar cn
      <$> traverse (checkRuleMetavarBinder lenv) rmbs
      <*> pure etn
      <*> pure fv
      <*> pure sfs'
      <*> pure jm'

  RuleReg cn rmbs fms jm outputs -> do

    let mjmv :: Map JudgementVariable (SymbolicTerm 'ResolvedVars)
        mjmv = M.fromList
                 [ (jmv,st)
                 | FormJudgement jmv _rbs
                     (Judgement _rtn _etn (SymFieldSort _loc _bs st:_sfs)) _outs <- fms
                 ]

    ((fms', jm', outputs'),lenv) <- flip runInfT defaultInfState $ do
      fms' <- traverse (checkFormula mbEtn mjmv) fms
      jm' <- checkJudgement mbEtn Nil jm
      outputs' <- traverse (checkOutput mbEtn mjmv) outputs

      pure (fms', jm', outputs')

    RuleReg cn
      <$> traverse (checkRuleMetavarBinder lenv) rmbs
      <*> pure fms'
      <*> pure jm'
      <*> pure outputs'

checkRuleMetavarBinder :: RelTcM m => InfState ->
  RuleMetavarBinder 'ResolvedVars -> m (RuleMetavarBinder 'Checked)
checkRuleMetavarBinder (InfState mbv msv _mev _mjmv) rmb = case rmb of
  RuleMetavarSort () sv
    | Just bs <- M.lookup sv msv -> pure (RuleMetavarSort bs sv)
    | otherwise -> throwError
        "KnotSpec.CheckRelations.checkRuleMetavarBinder.RuleMetavarSort"
  RuleMetavarFree fv -> pure (RuleMetavarFree fv)
  RuleMetavarBinding () bv
    | Just bs <- M.lookup bv mbv -> pure (RuleMetavarBinding bs bv)
    | otherwise -> throwError
        "KnotSpec.CheckRelations.checkRuleMetavarBinder.RuleMetavarBinding"
  RuleMetavarSet zv -> pure (RuleMetavarSet zv)

checkFormula :: (InfM m, RelTcM m) => Maybe EnvTypeName ->
  Map JudgementVariable (SymbolicTerm 'ResolvedVars) ->
  Formula 'ResolvedVars -> m (Formula 'Checked)
checkFormula _mbEtn _mjmv (FormLookup etn fv sfs) = do
  -- TODO: substitute bv somehow?
  (_bv,fds) <- lookupEnvClauseFields etn (fvNtn fv)
  sub <- makeFieldSubstitution fds sfs
  FormLookup etn fv
    <$> zipWithM (checkSymbolicField Nil sub) fds sfs
checkFormula mbEtn mjmv (FormJudgement jmv rbs jm outs)
  | Just etn <- mbEtn
  = do
      (inner,rbs') <- checkRuleBindSpec etn mjmv Nil rbs
      checkJudgementBindSpec jmv inner
      FormJudgement jmv rbs' <$> checkJudgement (Just etn) inner jm <*> pure outs
  | Nothing <- mbEtn, Nil <- rbs
  = FormJudgement jmv Nil <$> checkJudgement Nothing Nil jm <*> pure outs
  | otherwise
  = throwError "KnotSpec.CheckRelations.checkFormula"

checkRuleBindSpec :: (InfM m, RelTcM m) => EnvTypeName ->
  Map JudgementVariable (SymbolicTerm 'ResolvedVars) ->
  BindSpec 'Checked -> RuleBindSpec 'ResolvedVars ->
  m (BindSpec 'Checked, RuleBindSpec 'Checked)
checkRuleBindSpec _etn _mjmv outer Nil = return (outer, Nil)
checkRuleBindSpec etn mjmv outer (rbs :. rbsi) = do
  (bs',rbs') <- checkRuleBindSpec etn mjmv outer rbs
  (bs'',rbsi') <- checkRuleBindSpecItem etn mjmv bs' rbsi
  pure (bs'', rbs' :. rbsi')

checkRuleBindSpecItem :: (InfM m, RelTcM m) => EnvTypeName ->
  Map JudgementVariable (SymbolicTerm 'ResolvedVars) ->
  BindSpec 'Checked -> RuleBindSpecItem 'ResolvedVars ->
  m (BindSpec 'Checked, RuleBindSpecItem 'Checked)
checkRuleBindSpecItem etn mjmv outer rbsi =
  let fun = "KnotSpec.CheckRelations.checkRuleBindSpecItem" in case rbsi of
  RuleBsiBinding bv sfs -> do
    checkBindingBindSpec bv outer
    (bv',fds) <- lookupEnvClauseFields etn (bvNtn bv)
    sub <- makeFieldSubstitution fds sfs
    let sub' = sub <> mempty { subBindingVariables = M.singleton bv bv' }
    sfs' <- zipWithM (checkSymbolicField outer sub') fds sfs
    pure (outer :. BsiBinding bv, RuleBsiBinding bv sfs')
  RuleBsiCall fn jmv -> do
    checkJudgementBindSpec jmv outer
    st <- case M.lookup jmv mjmv of
            Just st -> pure st
            Nothing -> throwError . unlines $
                         [ fun ++ ".RuleBsiCall: can find judgement varialbe " <> show jmv <> " at call " <> show (fnLoc fn)
                         , show mjmv
                         ]
    inner <- symEvalFun outer fn st
    pure (inner, RuleBsiCall fn jmv)

checkJudgement :: (InfM m, RelTcM m) => Maybe EnvTypeName ->
  BindSpec 'Checked -> Judgement 'ResolvedVars ->
  m (Judgement 'Checked)
checkJudgement mbEtn outer (Judgement rtn () sfs) = do
  -- TODO: Decide whether there is a context and if it's of the same type.
  (_mbEtn',fds) <- lookupRelationFields rtn
  sub <- makeFieldSubstitution fds sfs
  sfs' <- zipWithM (checkSymbolicField outer sub) fds sfs
  pure $! Judgement rtn mbEtn sfs'

checkOutput :: (InfM m, RelTcM m) => Maybe EnvTypeName ->
  Map JudgementVariable (SymbolicTerm 'ResolvedVars) ->
  (FunName, RuleBindSpec 'ResolvedVars) ->
  m (FunName, RuleBindSpec 'Checked)
checkOutput (Just etn) mjmv (fn,rbs) =
  (,) fn . snd <$> checkRuleBindSpec etn mjmv Nil rbs
checkOutput Nothing _mjmv (_fn,_rbs) =
  throwError "KnotSpec.CheckRelations.checkOutput"

--------------------------------------------------------------------------------

data RelTcEnv =
  RelTcEnv
  { envConFields    :: Map
                         CtorName
                         ([FieldDecl 'WMV 'Checked 'Checked], SortTypeName)
  , envClauseFields :: Map
                         (EnvTypeName,NamespaceTypeName)
                         (BindingVariable, [FieldDecl 'WOMV 'Checked 'Checked])
  , envRelFields    :: Map
                         RelationTypeName
                         (Maybe EnvTypeName, [FieldDecl 'WOMV 'Checked 'Checked])
  }
  deriving Show

makeRelTcEnv :: TcM m =>
  [SortDecl 'Checked] -> [EnvDecl 'Checked] ->
  [RelationDecl 'ResolvedVars] -> m RelTcEnv
makeRelTcEnv sds eds rds = do

  relFields <- for rds $ \rd -> do
    lenv <- flip execInfT defaultInfState $
      for_ (rdIndices rd) $ \fd -> case fd of
        FieldDeclSort _loc bs sv -> infBindSpec Nil bs >>= checkSubtreeBindSpec sv
        FieldDeclEnv _loc bs ev -> infBindSpec Nil bs >>= checkEnvBindSpec ev
        FieldDeclSet{} -> return ()
    fds' <- traverse (checkFieldDecl lenv) (rdIndices rd)
    pure (rdTypeName rd, (rdEnv rd, fds'))

  pure $!
    RelTcEnv
      (M.fromList
         [ (cn,(fds, sdTypeName sd))
         | sd <- sds, CtorReg cn fds <- sdCtors sd
         ])
      (M.fromList
         [ ((edTypeName ed, typeNameOf bv),(bv, fds))
         | ed <- eds, EnvCtorCons _cn bv fds _mbRtn <- edCtors ed
         ])
      (M.fromList relFields)

newtype RelTcT m a = RelTcT { fromRelTcT :: ReaderT RelTcEnv m a }
  deriving (Functor, Applicative, Monad, MonadError e, MonadTrans, EnvM)

deriving instance EvalM m => EvalM (RelTcT m)
deriving instance TcM m => TcM (RelTcT m)

instance (TcM m, EvalM m) => RelTcM (RelTcT m) where
  lookupConstructorFields cn = RelTcT $ lookupEnv cn envConFields
    "KnotSpec.CheckRelations.RelTcM(RelTcT).lookupConType"
  lookupEnvClauseFields etn ntn = RelTcT $ lookupEnv (etn,ntn) envClauseFields
    "KnotSpec.CheckRelations.RelTcM(RelTcT).lookupEnvClauseFields"
  lookupRelationFields rtn = RelTcT $ lookupEnv rtn envRelFields
    "KnotSpec.CheckRelations.RelTcM(RelTcT).lookupRelationFields"

runRelTcT :: RelTcT m a -> RelTcEnv -> m a
runRelTcT = runReaderT . fromRelTcT
