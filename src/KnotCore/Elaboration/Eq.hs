{-# OPTIONS_GHC -fno-warn-orphans #-}

module KnotCore.Elaboration.Eq where

import Coq.StdLib
import Coq.Syntax

import KnotCore.DeBruijn.Core
import KnotCore.DeBruijn.Eq
import KnotCore.DeBruijn.Simplifier

import KnotCore.Elaboration.Core
import KnotCore.Syntax

import Control.Applicative
import Data.Maybe
import Data.Traversable(Traversable(..))

--------------------------------------------------------------------------------

instance TermLike EqHVL where
  toTerm = toTermInt . eqhSimplify
  toTermInt (EqhRefl h)               = TermApp eqRefl <$> sequenceA [toTermInt h]
  toTermInt (EqhSym eqh)              = eqSym <$> toTermInt eqh
  toTermInt (EqhTrans eqh1 eqh2)      = eqTrans <$> toTermInt eqh1 <*> toTermInt eqh2
  toTermInt (EqhCongAppend eqh1 eqh2) =
    eqFEqual2
    <$> (idAppendHVarlist >>= toRef)
    <*> toTermInt eqh1 <*> toTermInt eqh2
  toTermInt (EqhCongSucc _ntn eqh) =
    eqFEqual2
    <$> (idCtorHVarlistCons >>= toRef)
    <*> pure eqRefl
    <*> toTermInt eqh
  toTermInt (EqhShiftFun ntn fn _)    =
    TermApp
    <$> (idLemmaStabilityShift ntn fn >>= toRef)
    <*> pure [TermUnderscore,TermUnderscore]
  toTermInt (EqhSubstFun ntn fn _)    =
    TermApp
    <$> (idLemmaStabilitySubst ntn fn >>= toRef)
    <*> pure [TermUnderscore,TermUnderscore,TermUnderscore]
  toTermInt (EqhDomainAppend et1 et2) =
    TermApp
    <$> (idLemmaDomainEnvAppendEnv (typeNameOf et1) >>= toRef)
    <*> sequenceA
        [ toTerm et1
        , toTerm et2
        ]
  toTermInt (EqhDomainOutput fn jv et sts fnEts) =
    TermApp
    <$> (idLemmaDomainOutput (typeNameOf jv) fn >>= toRef)
    <*> sequenceA
        (toTerm et :
         map toTerm sts ++
         map (toTerm . snd) fnEts ++
         [toRef jv]
        )

instance TermLike EqCutoff where
  toTerm = toTermInt . eqcSimplify
  toTermInt (EqcRefl _)               = pure eqRefl
  toTermInt (EqcCongSucc eqc)       =
    eqFEqual
    <$> (idFamilyCutoffSucc >>= toRef)
    <*> toTermInt eqc
  toTermInt (EqcCongWeaken eqc eqh)   =
    eqFEqual2
    <$> (idFunctionWeakenCutoff (typeNameOf eqc) >>= toRef)
    <*> toTermInt eqc  <*> toTermInt eqh
  -- toTermInt (EqcCongShift _ _)        = error "NOT IMPLEMENTED"
  -- toTermInt (EqcCongShift' _ _)       = error "NOT IMPLEMENTED"
  -- toTermInt (EqcWeakenShift _)        = error "NOT IMPLEMENTED"
  -- toTermInt (EqcWeakenShift' _)       = error "NOT IMPLEMENTED"
  toTermInt (EqcWeakenAppend c h1 h2) =
    TermApp
    <$> (idLemmaWeakenCutoffAppend (typeNameOf c) >>= toRef)
    <*> sequenceA [toTermInt c, toTermInt h1, toTermInt h2]
  toTermInt (EqcSym eqc)              = eqSym <$> toTermInt eqc
  toTermInt (EqcTrans eqc1 eqc2)      = eqTrans <$> toTermInt eqc1 <*> toTermInt eqc2

instance TermLike EqTrace where
  toTerm = toTermInt . eqxSimplify
  toTermInt (EqxRefl _)             = pure eqRefl
  toTermInt (EqxCongSucc _ eqx)       =
    eqFEqual
    <$> (idFamilyTraceCons >>= toRef)
    <*> toTermInt eqx
  toTermInt (EqxCongWeaken eqx eqh)   =
    eqFEqual2
    <$> (idFunctionWeakenTrace >>= toRef)
    <*> toTermInt eqx  <*> toTermInt eqh
  toTermInt (EqxWeakenAppend x h1 h2) =
    TermApp
    <$> (idLemmaWeakenTraceAppend >>= toRef)
    <*> sequenceA
        [ toRef (typeNameOf x)
        , toTermInt x
        , toTermInt h1
        , toTermInt h2
        ]
  toTermInt (EqxSym eqx)              = eqSym <$> toTermInt eqx
  toTermInt (EqxTrans eqx1 eqx2)      = eqTrans <$> toTermInt eqx1 <*> toTermInt eqx2

instance TermLike EqTerm where
  toTerm = toTermInt . eqtSimplify
  toTermInt (EqtRefl _)               = pure eqRefl
  toTermInt (EqtAssumption _ tm)      = pure tm
  toTermInt (EqtCongWeaken eqt eqh)   =
    eqFEqual2
    <$> (idFunctionWeakenTerm (typeNameOf eqt) >>= toRef)
    <*> toTermInt eqt <*> toTermInt eqh
  toTermInt (EqtCongShift eqc eqt)    = do
    let ntn = typeNameOf eqc
        stn = typeNameOf eqt
    deps <- getSortNamespaceDependencies stn
    if ntn `elem` deps
      then eqFEqual2
           <$> (idFunctionShift (typeNameOf eqc) (typeNameOf eqt) >>= toRef)
           <*> toTermInt eqc  <*> toTermInt eqt
      else toTermInt eqt
  toTermInt (EqtCongSubst eqx eqts eqtt)    = do
    let ntn = typeNameOf eqx
        stn = typeNameOf eqtt
    deps <- getSortNamespaceDependencies stn
    if ntn `elem` deps
      then eqFEqual3
           <$> (idFunctionSubst (typeNameOf eqx) (typeNameOf eqtt) >>= toRef)
           <*> toTermInt eqx <*> toTermInt eqts <*> toTermInt eqtt
      else toTermInt eqtt
  toTermInt (EqtSym eqt)                     = eqSym <$> toTermInt eqt
  toTermInt (EqtTrans eqt1 eqt2)             = eqTrans <$> toTermInt eqt1 <*> toTermInt eqt2
  toTermInt (EqtCongCtor _ cn eqts)          = eqFEqualn <$> toRef cn <*> traverse toTermInt eqts
  toTermInt (EqtCommShiftShift0 ste c ntnw)  = do
    let stn  = typeNameOf ste
        ntnc = typeNameOf c
    deps <- getSortNamespaceDependencies stn
    if ntnc `elem` deps && ntnw `elem` deps
      then TermApp
             <$> (idLemmaShiftComm ntnc ntnw stn >>= toRef)
             <*> -- TODO: properly elaborate symbolic term
                 pure [TermUnderscore, TermUnderscore]
      else toTermInt (EqtRefl stn)
  toTermInt (EqtCommShiftSubst0 ste c ntn st) =
    TermApp
    <$> (idLemmaShiftSubstComm (typeNameOf c) ntn (typeNameOf ste) >>= toRef)
    <*> sequenceA
        [ toTermInt ste
        , toTermInt c
        , toTermInt st
        ]
  toTermInt (EqtCommSubstShift0 ste x subSt ntnw)  = do
    let stn  = typeNameOf ste
        ntnc = typeNameOf x
    deps <- getSortNamespaceDependencies stn
    if ntnc `elem` deps && ntnw `elem` deps
      then TermApp
             <$> (idLemmaSubstShiftComm ntnc ntnw stn >>= toRef)
             <*> -- TODO: properly elaborate symbolic term
                 pure [TermUnderscore, TermUnderscore, TermUnderscore]
      else toTermInt (EqtRefl stn)
  toTermInt (EqtCommSubstSubst0 ste x subSt ntn st) =
    TermApp
    <$> (idLemmaSubstSubstComm (typeNameOf x) ntn (typeNameOf ste) >>= toRef)
    <*> sequenceA
        [ toTermInt ste
        , toTermInt x
        , toTermInt subSt
        , toTermInt st
        ]
  toTermInt (EqtCommWeakenShift h c st) = do
    let stn  = typeNameOf st
        ntnc = typeNameOf c
    deps <- getSortNamespaceDependencies stn
    if ntnc `elem` deps
      then TermApp
           <$> (idLemmaWeakenShift (typeNameOf c) (typeNameOf st) >>= toRef)
           <*> sequenceA
               [ toTermInt h
               , toTermInt c
               , toTermInt st
               ]
      else toTermInt (EqtRefl stn)
  toTermInt (EqtCommWeakenSubst h x subSt st) = do
    let stn  = typeNameOf st
        ntnc = typeNameOf x
    deps <- getSortNamespaceDependencies stn
    if ntnc `elem` deps
      then TermApp
           <$> (idLemmaWeakenSubst (typeNameOf x) (typeNameOf st) >>= toRef)
           <*> sequenceA
               [ toTermInt h
               , toTermInt x
               , toTermInt subSt
               , toTermInt st
               ]
      else toTermInt (EqtRefl stn)

instance TermLike EqETerm where
  toTerm = toTermInt . eqeSimplify
  toTermInt (EqeRefl _) = pure eqRefl
  toTermInt (EqeSym eqe) = eqSym <$> toTermInt eqe
  toTermInt (EqeTrans eqe1 eqe2) = eqTrans <$> toTermInt eqe1 <*> toTermInt eqe2
  toTermInt (EqeCongAppend eqe1 eqe2) =
    eqFEqual2
      <$> (idFunctionAppendEnv (typeNameOf eqe1) >>= toRef)
      <*> toTermInt eqe1 <*> toTermInt eqe2
  toTermInt (EqeShiftAppend c et1 et2) = do
    let etn  = typeNameOf et1
        ntnc = typeNameOf c
    deps <- getEnvNamespaceDependencies etn
    if ntnc `elem` deps
      then TermApp
           <$> (idLemmaShiftEnvAppendEnv (typeNameOf c) (typeNameOf et1) >>= toRef)
           <*> sequence [ toTerm c, toTerm et1, toTerm et2 ]
      else toTermInt (EqeRefl (EAppend et1 et2))
  toTermInt (EqeSubstAppend x subSt et1 et2) = do
    let etn  = typeNameOf et1
        ntnc = typeNameOf x
    deps <- getEnvNamespaceDependencies etn
    if ntnc `elem` deps
      then TermApp
           <$> (idLemmaSubstEnvAppendEnv (typeNameOf x) (typeNameOf et1) >>= toRef)
           <*> sequence [ toTerm x, toTerm subSt, toTerm et1, toTerm et2 ]
      else toTermInt (EqeRefl (EAppend et1 et2))


eqhvlEvalBindspecShift :: Elab m => NamespaceTypeName -> BindSpec -> m EqHVL
eqhvlEvalBindspecShift ntn bs' = case bs' of
  Nil -> pure (EqhRefl HV0)
  bs :. BsiBinding mv ->
    EqhCongAppend
      <$> eqhvlEvalBindspecShift ntn bs
      <*> pure (EqhRefl (HVS (typeNameOf mv) HV0))
  _bs :. BsiCall fn sv -> do
    deps <- getSortNamespaceDependencies (typeNameOf sv)
    if ntn `elem` deps
      then pure (EqhShiftFun ntn fn sv)
      else pure (EqhRefl (HVCall fn (SVar sv)))

eqhvlEvalBindspecSubst :: Elab m => NamespaceTypeName -> BindSpec -> m EqHVL
eqhvlEvalBindspecSubst ntn bs =
  case bs of
    Nil       -> pure (EqhRefl HV0)
    bs :. bsi ->
       EqhCongAppend
       <$> case bsi of
             BsiBinding mv -> pure (EqhRefl (HVS (typeNameOf mv) HV0))
             BsiCall fn sv -> do
               deps <- getSortNamespaceDependencies (typeNameOf sv)
               if ntn `elem` deps
                 then pure $ EqhSubstFun ntn fn sv
                 else pure (EqhRefl (HVCall fn (SVar sv)))
       <*> eqhvlEvalBindspecSubst ntn bs

eqhvlRuleBindSpecDomain :: ElabRuleM m => EnvTypeName -> RuleBindSpec -> m EqHVL
eqhvlRuleBindSpecDomain _etn Nil = pure (EqhRefl HV0)
eqhvlRuleBindSpecDomain etn (rbs :. rbsi) = case rbsi of
  RuleBsiBinding mv _sts ->
    EqhCongSucc (typeNameOf mv) <$> eqhvlRuleBindSpecDomain etn rbs
  RuleBsiCall fn jv -> do
    (_jmtRbs,Judgement _rtn (Just se) sfs outs) <- lookupJudgement jv
    fnJvEv <- lookupJudgementOutput fn jv
    EqhTrans
      <$> (EqhDomainAppend
            <$> evalRuleBindSpec (ENil etn) rbs
            <*> pure (EVar fnJvEv)
          )
      <*> (EqhCongAppend
            <$> eqhvlRuleBindSpecDomain etn rbs
            <*> (EqhDomainOutput fn jv
                 <$> symbolicEnvToETerm se
                 <*> (catMaybes <$> traverse symbolicFieldToField sfs)
                 <*> traverse (\(fn,out) -> (,) fn <$> symbolicEnvToETerm out) outs
                )
          )


eqhvlRuleBindSpecShift :: ElabRuleM m => Cutoff -> ETerm -> RuleBindSpec -> m EqETerm
eqhvlRuleBindSpecShift _c et Nil = pure (EqeRefl et)
eqhvlRuleBindSpecShift c et (rbs :. rbsi) = case rbsi of
  RuleBsiBinding mv sts -> do
    let ntn = typeNameOf mv
    pure (EqeRefl (ENil (typeNameOf et)))
    -- EqeCongSucc ntn et <$> eqhvlRuleBindSpecShift (CS' ntn c) (ECons et ntn sts) rbs
  RuleBsiCall fn jv -> do
    (_jmtRbs,Judgement _rtn (Just se) sts outs) <- lookupJudgement jv
    fnJvEv <- lookupJudgementOutput fn jv
    pre <- evalRuleBindSpec et rbs
    EqeTrans
      <$> pure (EqeShiftAppend c pre (EVar fnJvEv))
      <*> (EqeCongAppend
            <$> eqhvlRuleBindSpecShift c et rbs
            <*> pure (EqeRefl (EShift' (CWeaken c (HVDomainEnv pre)) (EVar fnJvEv)))
          )

eqhvlRuleBindSpecSubst :: ElabRuleM m => Trace -> STerm -> ETerm -> RuleBindSpec -> m EqETerm
eqhvlRuleBindSpecSubst _x subSt et Nil = pure (EqeRefl et)
eqhvlRuleBindSpecSubst x subSt et (rbs :. rbsi) = case rbsi of
  RuleBsiBinding mv sts -> do
    let ntn = typeNameOf mv
    pure (EqeRefl (ENil (typeNameOf et)))
    -- EqeCongSucc ntn et <$> eqhvlRuleBindSpecShift (CS' ntn c) (ECons et ntn sts) rbs
  RuleBsiCall fn jv -> do
    (_jmtRbs,Judgement _rtn (Just se) sts outs) <- lookupJudgement jv
    fnJvEv <- lookupJudgementOutput fn jv
    pre <- evalRuleBindSpec et rbs
    EqeTrans
      <$> pure (EqeSubstAppend x subSt pre (EVar fnJvEv))
      <*> (EqeCongAppend
            <$> eqhvlRuleBindSpecSubst x subSt et rbs
            <*> pure (EqeRefl (ESubst' (TWeaken x (HVDomainEnv pre)) subSt (EVar fnJvEv)))
          )
