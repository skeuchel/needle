{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wall -fno-warn-name-shadowing #-}

module KnotCore.DeBruijn.Eq where

import KnotCore.DeBruijn.Core
import KnotCore.DeBruijn.Simplifier
import KnotCore.Syntax

import Coq.Syntax

data EqHVL
  = EqhRefl HVarlist
  | EqhShiftFun NamespaceTypeName FunName SortVariable
  | EqhSubstFun NamespaceTypeName FunName SortVariable
  | EqhCongAppend EqHVL EqHVL
  | EqhCongSucc NamespaceTypeName EqHVL
  | EqhSym EqHVL
  | EqhTrans EqHVL EqHVL
  | EqhDomainAppend ETerm ETerm
  | EqhDomainOutput FunName JudgementVariable ETerm [Field 'WOMV] [(FunName,ETerm)]
  deriving (Eq,Ord,Show)

data EqCutoff
  = EqcRefl NamespaceTypeName
  -- | EqcWeakenShift NamespaceTypeName
  -- | EqcWeakenShift' NamespaceTypeName
  | EqcWeakenAppend Cutoff HVarlist HVarlist
  | EqcCongSucc EqCutoff
  | EqcCongWeaken EqCutoff EqHVL
  -- | EqcCongShift EqCutoff EqCutoff
  -- | EqcCongShift' EqCutoff EqCutoff
  | EqcSym EqCutoff
  | EqcTrans EqCutoff EqCutoff
  deriving (Eq,Ord,Show)

instance TypeNameOf EqCutoff NamespaceTypeName where
  typeNameOf (EqcRefl ntn)           = ntn
  -- typeNameOf (EqcWeakenShift ntn)    = ntn
  -- typeNameOf (EqcWeakenShift' ntn)   = ntn
  typeNameOf (EqcWeakenAppend c _ _) = typeNameOf c
  typeNameOf (EqcCongSucc eqc)       = typeNameOf eqc
  typeNameOf (EqcCongWeaken eqc _)   = typeNameOf eqc
  -- typeNameOf (EqcCongShift eqc _)    = typeNameOf eqc
  -- typeNameOf (EqcCongShift' eqc _)   = typeNameOf eqc
  typeNameOf (EqcSym eqc)            = typeNameOf eqc
  typeNameOf (EqcTrans eqc _)        = typeNameOf eqc

data EqTrace
  = EqxRefl NamespaceTypeName
  | EqxCongSucc NamespaceTypeName EqTrace
  | EqxCongWeaken EqTrace EqHVL
  | EqxWeakenAppend Trace HVarlist HVarlist
  | EqxSym EqTrace
  | EqxTrans EqTrace EqTrace
  deriving (Eq,Ord,Show)

instance TypeNameOf EqTrace NamespaceTypeName where
  typeNameOf (EqxRefl ntn)           = ntn
  typeNameOf (EqxWeakenAppend x _ _) = typeNameOf x
  typeNameOf (EqxCongSucc _ eqx)     = typeNameOf eqx
  typeNameOf (EqxCongWeaken eqx _)   = typeNameOf eqx
  typeNameOf (EqxSym eqx)            = typeNameOf eqx
  typeNameOf (EqxTrans eqx _)        = typeNameOf eqx

data EqTerm
  = EqtRefl SortTypeName
  | EqtAssumption SortTypeName Term
  | EqtCongWeaken EqTerm EqHVL
  | EqtCongShift EqCutoff EqTerm
  | EqtCongSubst EqTrace EqTerm EqTerm
  | EqtSym EqTerm
  | EqtTrans EqTerm EqTerm
  | EqtCongCtor SortTypeName CtorName [EqTerm]
  | EqtCommShiftShift0 STerm Cutoff NamespaceTypeName
  | EqtCommShiftSubst0 STerm Cutoff NamespaceTypeName STerm
  | EqtCommSubstShift0 STerm Trace STerm NamespaceTypeName
  | EqtCommSubstSubst0 STerm Trace STerm NamespaceTypeName STerm
  | EqtCommWeakenShift HVarlist Cutoff STerm
  | EqtCommWeakenSubst HVarlist Trace STerm STerm
  deriving (Eq,Ord,Show)

instance TypeNameOf EqTerm SortTypeName where
  typeNameOf (EqtRefl stn)                    = stn
  typeNameOf (EqtAssumption stn _)            = stn
  typeNameOf (EqtCongWeaken eqt _)            = typeNameOf eqt
  typeNameOf (EqtCongShift _ eqt)             = typeNameOf eqt
  typeNameOf (EqtCongSubst _ _ eqt)           = typeNameOf eqt
  typeNameOf (EqtSym eqt)                     = typeNameOf eqt
  typeNameOf (EqtTrans eqt _)                 = typeNameOf eqt
  typeNameOf (EqtCongCtor stn _ _)            = stn
  typeNameOf (EqtCommShiftShift0 ste _ _)     = typeNameOf ste
  typeNameOf (EqtCommShiftSubst0 ste _ _ _)   = typeNameOf ste
  typeNameOf (EqtCommSubstShift0 ste _ _ _)   = typeNameOf ste
  typeNameOf (EqtCommSubstSubst0 ste _ _ _ _) = typeNameOf ste
  typeNameOf (EqtCommWeakenShift _ _ ste)     = typeNameOf ste
  typeNameOf (EqtCommWeakenSubst _ _ _ ste)   = typeNameOf ste

data EqETerm
  = EqeRefl ETerm
  | EqeSym EqETerm
  | EqeTrans EqETerm EqETerm
  | EqeCongAppend EqETerm EqETerm
  -- | EqeCongSucc NamespaceTypeName EqETerm [EqTerm]
  | EqeShiftAppend Cutoff ETerm ETerm
  | EqeSubstAppend Trace STerm ETerm ETerm
  deriving (Eq,Ord,Show)

instance TypeNameOf EqETerm EnvTypeName where
  typeNameOf (EqeRefl et)                     = typeNameOf et
  typeNameOf (EqeSym eqe)                     = typeNameOf eqe
  typeNameOf (EqeTrans eqe1 _eqe2)            = typeNameOf eqe1
  typeNameOf (EqeCongAppend eqe1 _eqe2)       = typeNameOf eqe1
  -- typeNameOf (EqeCongSucc _ntn eqe _sts)      = typeNameOf eqe
  typeNameOf (EqeShiftAppend _c et1 _et2)     = typeNameOf et1
  typeNameOf (EqeSubstAppend _c _st et1 _et2) = typeNameOf et1

{-
   ___      _  ___   ___
  | __|__ _| || \ \ / / |
  | _|/ _` | __ |\ V /| |__
  |___\__, |_||_| \_/ |____|
         |_|
-}

isEqhRefl :: EqHVL -> Bool
isEqhRefl (EqhRefl _) = True
isEqhRefl _           = False

eqhSimplifyTrans :: EqHVL -> EqHVL -> EqHVL
eqhSimplifyTrans (EqhRefl _)        e2          = e2
eqhSimplifyTrans e1                 (EqhRefl _) = e1
eqhSimplifyTrans (EqhTrans e11 e12) e2          = eqhSimplifyTrans e11 (eqhSimplifyTrans e12 e2)
eqhSimplifyTrans e1                 e2          = EqhTrans e1 e2

eqhSimplifyCongAppend :: EqHVL -> EqHVL -> EqHVL
eqhSimplifyCongAppend (EqhRefl h1) (EqhRefl h2) = EqhRefl (simplifyHvlAppend h1 h2)
eqhSimplifyCongAppend e1           e2           = EqhCongAppend e1 e2

eqhSimplifyCongSucc :: NamespaceTypeName -> EqHVL -> EqHVL
eqhSimplifyCongSucc ntn (EqhRefl h) = EqhRefl (HVS ntn h)
eqhSimplifyCongSucc ntn e           = EqhCongSucc ntn e

eqhSimplifyDomainAppend :: ETerm -> ETerm -> EqHVL
eqhSimplifyDomainAppend et1 et2 =
  case et2 of
    ENil _etn -> EqhRefl (HVDomainEnv et1)
    ECons et2' ntn _sts -> eqhSimplifyCongSucc ntn (eqhSimplifyDomainAppend et1 et2')
    _        -> EqhDomainAppend et1 et2

eqhSimplifyDomainAppendSym :: ETerm -> ETerm -> EqHVL
eqhSimplifyDomainAppendSym et1 et2 =
  case et2 of
    ENil _etn -> EqhRefl (HVDomainEnv et1)
    _         -> EqhSym (EqhDomainAppend et1 et2)

eqhSimplify :: EqHVL -> EqHVL
eqhSimplify eqh =
  case eqh of
    EqhRefl h                           ->  EqhRefl (simplifyHvl h)
    EqhSym e                            ->  eqhSimplifySym e
    EqhTrans e1 e2                      ->  eqhSimplifyTrans (eqhSimplify e1) (eqhSimplify e2)
    EqhCongAppend e1 e2                 ->  eqhSimplifyCongAppend (eqhSimplify e1) (eqhSimplify e2)
    EqhCongSucc ntn e                   ->  eqhSimplifyCongSucc ntn (eqhSimplify e)
    EqhShiftFun ntn fn sv               ->  EqhShiftFun ntn fn sv
    EqhSubstFun ntn fn sv               ->  EqhSubstFun ntn fn sv
    EqhDomainAppend et1 et2             ->  eqhSimplifyDomainAppend (simplifyETerm et1) (simplifyETerm et2)
    EqhDomainOutput fn jv et sts fnEts  ->  EqhDomainOutput fn jv et sts fnEts

eqhSimplifySym :: EqHVL -> EqHVL
eqhSimplifySym eqh =
  case eqh of
    EqhRefl h                           ->  EqhRefl (simplifyHvl h)
    EqhSym e                            ->  eqhSimplify e
    EqhTrans e1 e2                      ->  eqhSimplifyTrans (eqhSimplifySym e2) (eqhSimplifySym e1)
    EqhCongAppend e1 e2                 ->  eqhSimplifyCongAppend (eqhSimplifySym e1) (eqhSimplifySym e2)
    EqhCongSucc ntn e                   ->  eqhSimplifyCongSucc ntn (eqhSimplifySym e)
    EqhShiftFun ntn fn sv               ->  EqhSym (EqhShiftFun ntn fn sv)
    EqhSubstFun ntn fn sv               ->  EqhSym (EqhSubstFun ntn fn sv)
    EqhDomainAppend et1 et2             ->  eqhSimplifyDomainAppendSym (simplifyETerm et1) (simplifyETerm et2)
    EqhDomainOutput fn jv et sts fnEts  ->  EqhSym (EqhDomainOutput fn jv et sts fnEts)

{-
   ___       ___     _        __  __
  | __|__ _ / __|  _| |_ ___ / _|/ _|
  | _|/ _` | (_| || |  _/ _ \  _|  _|
  |___\__, |\___\_,_|\__\___/_| |_|
         |_|
-}

eqcSimplifyCongSucc :: EqCutoff -> EqCutoff
eqcSimplifyCongSucc ec =
  case ec of
    EqcRefl  ntn -> EqcRefl ntn
    ec           -> EqcCongSucc ec

eqcSimplifyWeakenAppend :: Cutoff -> HVarlist -> HVarlist -> EqCutoff
eqcSimplifyWeakenAppend c h1 h2 =
  case h2 of
    HV0                     -> EqcRefl (typeNameOf c)
    HVS ntn h2
      | typeNameOf c == ntn -> eqcSimplifyCongSucc (eqcSimplifyWeakenAppend c h1 h2)
      | otherwise           -> eqcSimplifyWeakenAppend c h1 h2
    h2                      -> EqcWeakenAppend (simplifyCutoff c) (simplifyHvl h1) h2

eqcSimplifySymWeakenAppend :: Cutoff -> HVarlist -> HVarlist -> EqCutoff
eqcSimplifySymWeakenAppend c h1 h2 =
  case h2 of
    HV0                     -> EqcRefl (typeNameOf c)
    HVS ntn h2
      | typeNameOf c == ntn -> eqcSimplifyCongSucc (eqcSimplifyWeakenAppend c h1 h2)
      | otherwise           -> eqcSimplifyWeakenAppend c h1 h2
    h2                      -> EqcSym (EqcWeakenAppend (simplifyCutoff c) (simplifyHvl h1) h2)

eqcSimplifyTrans :: EqCutoff -> EqCutoff -> EqCutoff
eqcSimplifyTrans (EqcRefl _)        e2          = e2
eqcSimplifyTrans e1                 (EqcRefl _) = e1
eqcSimplifyTrans (EqcTrans e11 e12) e2          = eqcSimplifyTrans e11 (eqcSimplifyTrans e12 e2)
eqcSimplifyTrans e1                 e2          = EqcTrans e1 e2

eqcSimplifyCongWeaken :: EqCutoff -> EqHVL -> EqCutoff
eqcSimplifyCongWeaken ec eh =
  case (ec,eh) of
    (EqcRefl stn , EqhRefl _) -> EqcRefl stn
    (ec          , eh       ) -> EqcCongWeaken ec eh

eqcSimplify :: EqCutoff -> EqCutoff
eqcSimplify eqc =
  case eqc of
    EqcRefl ntn         -> EqcRefl ntn
    EqcSym e            -> eqcSimplifySym e
    EqcTrans e1 e2      -> eqcSimplifyTrans (eqcSimplify e1) (eqcSimplify e2)
    EqcCongSucc ec      -> eqcSimplifyCongSucc (eqcSimplify ec)
    EqcCongWeaken ec eh ->
      case (eqcSimplify ec, eqhSimplify eh) of
        (EqcRefl  ntn       , EqhRefl _ ) -> EqcRefl ntn
        (ec'                , eh'       ) -> EqcCongWeaken ec' eh'
    -- EqcCongShift e1 e2 ->
    --   case (eqcSimplify e1, eqcSimplify e2) of
    --     (EqcRefl ntn        , EqcRefl _ ) -> EqcRefl ntn
    --     (e1'                , e2'       ) -> EqcCongShift e1' e2'
    -- EqcCongShift' e1 e2 ->
    --   case (eqcSimplify e1, eqcSimplify e2) of
    --     (EqcRefl ntn        , EqcRefl _ ) -> EqcRefl ntn
    --     (e1'                , e2'       ) -> EqcCongShift' e1' e2'
    -- EqcWeakenShift ntn       -> EqcWeakenShift ntn
    -- EqcWeakenShift' ntn      -> EqcWeakenShift' ntn
    EqcWeakenAppend c h1 h2  -> eqcSimplifyWeakenAppend c h1 (simplifyHvl h2)

eqcSimplifySym :: EqCutoff -> EqCutoff
eqcSimplifySym eqc =
  case eqc of
    EqcRefl ntn         -> EqcRefl ntn
    EqcSym e            -> eqcSimplify e
    EqcTrans e1 e2      -> eqcSimplifyTrans (eqcSimplifySym e2) (eqcSimplifySym e1)
    EqcCongSucc   ec    -> eqcSimplifyCongSucc (eqcSimplifySym ec)
    EqcCongWeaken ec eh ->
      case (eqcSimplifySym ec, eqhSimplifySym eh) of
        (EqcRefl  ntn       , EqhRefl _ ) -> EqcRefl ntn
        (ec'                , eh'       ) -> EqcCongWeaken ec' eh'
    -- EqcCongShift e1 e2 ->
    --   case (eqcSimplifySym e1, eqcSimplifySym e2) of
    --     (EqcRefl ntn        , EqcRefl _ ) -> EqcRefl ntn
    --     (e1'                , e2'       ) -> EqcCongShift e1' e2'
    -- EqcCongShift' e1 e2 ->
    --   case (eqcSimplifySym e1, eqcSimplifySym e2) of
    --     (EqcRefl ntn        , EqcRefl _ ) -> EqcRefl ntn
    --     (e1'                , e2'       ) -> EqcCongShift' e1' e2'
    -- EqcWeakenShift ntn       -> EqcSym (EqcWeakenShift ntn)
    -- EqcWeakenShift' ntn      -> EqcSym (EqcWeakenShift' ntn)
    EqcWeakenAppend c h1 h2  -> eqcSimplifySymWeakenAppend c h1 (simplifyHvl h2)

{-
 ___     _____
| __|__ |_   _| _ __ _ __ ___
| _|/ _` || || '_/ _` / _/ -_)
|___\__, ||_||_| \__,_\__\___|
       |_|
-}

eqxSimplifyCongSucc :: NamespaceTypeName -> EqTrace -> EqTrace
eqxSimplifyCongSucc ntnb ec =
  case ec of
    EqxRefl  ntn -> EqxRefl ntn
    ec           -> EqxCongSucc ntnb ec

eqxSimplifyWeakenAppend :: Trace -> HVarlist -> HVarlist -> EqTrace
eqxSimplifyWeakenAppend c h1 h2 =
  case h2 of
    HV0                     -> EqxRefl (typeNameOf c)
    -- HVS ntn h2
    --   | typeNameOf c == ntn -> eqxSimplifyCongSucc (eqxSimplifyWeakenAppend c h1 h2)
    --   | otherwise           -> eqxSimplifyWeakenAppend c h1 h2
    h2                      -> EqxWeakenAppend (simplifyTrace c) (simplifyHvl h1) h2

eqxSimplifySymWeakenAppend :: Trace -> HVarlist -> HVarlist -> EqTrace
eqxSimplifySymWeakenAppend c h1 h2 =
  case h2 of
    HV0                     -> EqxRefl (typeNameOf c)
    -- HVS ntn h2
    --   | typeNameOf c == ntn -> eqxSimplifyCongSucc (eqxSimplifyWeakenAppend c h1 h2)
    --   | otherwise           -> eqxSimplifyWeakenAppend c h1 h2
    h2                      -> EqxSym (EqxWeakenAppend (simplifyTrace c) (simplifyHvl h1) h2)

eqxSimplifyTrans :: EqTrace -> EqTrace -> EqTrace
eqxSimplifyTrans (EqxRefl _)        e2          = e2
eqxSimplifyTrans e1                 (EqxRefl _) = e1
eqxSimplifyTrans (EqxTrans e11 e12) e2          = eqxSimplifyTrans e11 (eqxSimplifyTrans e12 e2)
eqxSimplifyTrans e1                 e2          = EqxTrans e1 e2

eqxSimplifyCongWeaken :: EqTrace -> EqHVL -> EqTrace
eqxSimplifyCongWeaken ec eh =
  case (ec,eh) of
    (EqxRefl stn , EqhRefl _) -> EqxRefl stn
    (ec          , eh       ) -> EqxCongWeaken ec eh

eqxSimplify :: EqTrace -> EqTrace
eqxSimplify eqx =
  case eqx of
    EqxRefl ntn         -> EqxRefl ntn
    EqxSym e            -> eqxSimplifySym e
    EqxTrans e1 e2      -> eqxSimplifyTrans (eqxSimplify e1) (eqxSimplify e2)
    EqxCongSucc ntnb ec -> eqxSimplifyCongSucc ntnb (eqxSimplify ec)
    EqxCongWeaken ec eh ->
      case (eqxSimplify ec, eqhSimplify eh) of
        (EqxRefl  ntn       , EqhRefl _ ) -> EqxRefl ntn
        (ec'                , eh'       ) -> EqxCongWeaken ec' eh'
    EqxWeakenAppend c h1 h2  -> eqxSimplifyWeakenAppend c h1 (simplifyHvl h2)

eqxSimplifySym :: EqTrace -> EqTrace
eqxSimplifySym eqx =
  case eqx of
    EqxRefl ntn         -> EqxRefl ntn
    EqxSym e            -> eqxSimplify e
    EqxTrans e1 e2      -> eqxSimplifyTrans (eqxSimplifySym e2) (eqxSimplifySym e1)
    EqxCongSucc ntnb ec -> eqxSimplifyCongSucc ntnb (eqxSimplifySym ec)
    EqxCongWeaken ec eh ->
      case (eqxSimplifySym ec, eqhSimplifySym eh) of
        (EqxRefl  ntn       , EqhRefl _ ) -> EqxRefl ntn
        (ec'                , eh'       ) -> EqxCongWeaken ec' eh'
    EqxWeakenAppend c h1 h2  -> eqxSimplifySymWeakenAppend c h1 (simplifyHvl h2)

{-
 ___     _____
| __|__ |_   _|__ _ _ _ __
| _|/ _` || |/ -_) '_| '  \
|___\__, ||_|\___|_| |_|_|_|
       |_|
-}

eqtSimplifyTrans :: EqTerm -> EqTerm -> EqTerm
eqtSimplifyTrans (EqtRefl _)        e2          = e2
eqtSimplifyTrans e1                 (EqtRefl _) = e1
eqtSimplifyTrans (EqtTrans e11 e12) e2          = eqtSimplifyTrans e11 (eqtSimplifyTrans e12 e2)
eqtSimplifyTrans e1                 e2          = EqtTrans e1 e2

eqtSimplifyCongWeaken :: EqTerm -> EqHVL -> EqTerm
eqtSimplifyCongWeaken et eh =
  case (et,eh) of
    (EqtRefl stn , EqhRefl _) -> EqtRefl stn
    (et          , eh       ) -> EqtCongWeaken et eh

isEqtRefl :: EqTerm -> Bool
isEqtRefl (EqtRefl _) = True
isEqtRefl _           = False

eqtSimplify :: EqTerm -> EqTerm
eqtSimplify eqt =
  case eqt of
    EqtRefl stn         -> EqtRefl stn
    EqtSym e            -> eqtSimplifySym e
    EqtTrans e1 e2      -> eqtSimplifyTrans (eqtSimplify e1) (eqtSimplify e2)
    EqtCongWeaken et eh -> eqtSimplifyCongWeaken (eqtSimplify et) (eqhSimplify eh)
    EqtCongShift ec et ->
      case (eqcSimplify ec, eqtSimplify et) of
        (EqcRefl _          , EqtRefl stn  ) -> EqtRefl stn
        (ec'                , et'          ) -> EqtCongShift ec' et'
    EqtCongSubst ex es et ->
      case (eqxSimplify ex, eqtSimplify es, eqtSimplify et) of
        (EqxRefl _ , EqtRefl _ , EqtRefl stn  ) -> EqtRefl stn
        (ex'       , es'       , et'          ) -> EqtCongSubst ex' es' et'
    EqtAssumption stn tm -> EqtAssumption stn tm
    EqtCongCtor stn cn ets ->
      let ets' = map eqtSimplify ets
      in if Prelude.all isEqtRefl ets'
           then EqtRefl stn
           else EqtCongCtor stn cn ets'
    EqtCommShiftShift0 ste c ntn          -> EqtCommShiftShift0 ste (simplifyCutoff c) ntn
    EqtCommShiftSubst0 ste c ntn st       -> EqtCommShiftSubst0 ste (simplifyCutoff c) ntn st
    EqtCommSubstShift0 ste x subSt ntn    -> EqtCommSubstShift0 ste (simplifyTrace x) subSt ntn
    EqtCommSubstSubst0 ste x subSt ntn st -> EqtCommSubstSubst0 ste (simplifyTrace x) subSt ntn st
    EqtCommWeakenShift hvl c ste          -> EqtCommWeakenShift (simplifyHvl hvl) (simplifyCutoff c) ste
    EqtCommWeakenSubst hvl x subSt ste    -> EqtCommWeakenSubst (simplifyHvl hvl) (simplifyTrace x) subSt ste

eqtSimplifySym :: EqTerm -> EqTerm
eqtSimplifySym eqt =
  case eqt of
    EqtRefl stn         -> EqtRefl stn
    EqtSym e            -> eqtSimplify e
    EqtTrans e1 e2      -> eqtSimplifyTrans (eqtSimplifySym e2) (eqtSimplifySym e1)
    EqtCongWeaken et eh -> eqtSimplifyCongWeaken (eqtSimplifySym et) (eqhSimplifySym eh)
    EqtCongShift ec et ->
      case (eqcSimplifySym ec, eqtSimplifySym et) of
        (EqcRefl _          , EqtRefl stn  ) -> EqtRefl stn
        (ec'                , et'          ) -> EqtCongShift ec' et'
    EqtCongSubst ex es et ->
      case (eqxSimplifySym ex, eqtSimplifySym es, eqtSimplifySym et) of
        (EqxRefl _ , EqtRefl _ , EqtRefl stn  ) -> EqtRefl stn
        (ex'       , es'       , et'          ) -> EqtCongSubst ex' es' et'
    EqtAssumption stn tm -> EqtAssumption stn tm
    EqtCongCtor stn cn ets ->
      let ets' = map eqtSimplifySym ets
      in if Prelude.all isEqtRefl ets'
           then EqtRefl stn
           else EqtCongCtor stn cn ets'
    EqtCommShiftShift0 ste c ntn          -> EqtSym (EqtCommShiftShift0 ste (simplifyCutoff c) ntn)
    EqtCommShiftSubst0 ste c ntn st       -> EqtSym (EqtCommShiftSubst0 ste (simplifyCutoff c) ntn st)
    EqtCommSubstShift0 ste x subSt ntn    -> EqtSym (EqtCommSubstShift0 ste (simplifyTrace x) subSt ntn)
    EqtCommSubstSubst0 ste x subSt ntn st -> EqtSym (EqtCommSubstSubst0 ste (simplifyTrace x) subSt ntn st)
    EqtCommWeakenShift hvl c ste          -> EqtSym (EqtCommWeakenShift (simplifyHvl hvl) (simplifyCutoff c) ste)
    EqtCommWeakenSubst hvl x subSt ste    -> EqtSym (EqtCommWeakenSubst (simplifyHvl hvl) (simplifyTrace x) subSt ste)

{-
 ___      ___ _____
| __|__ _| __|_   _|__ _ _ _ __
| _|/ _` | _|  | |/ -_) '_| '  \
|___\__, |___| |_|\___|_| |_|_|_|
       |_|
-}

isEqeRefl :: EqETerm -> Bool
isEqeRefl (EqeRefl _) = True
isEqeRefl _           = False

eqeSimplifyTrans :: EqETerm -> EqETerm -> EqETerm
eqeSimplifyTrans (EqeRefl _)        e2          = e2
eqeSimplifyTrans e1                 (EqeRefl _) = e1
eqeSimplifyTrans (EqeTrans e11 e12) e2          = eqeSimplifyTrans e11 (eqeSimplifyTrans e12 e2)
eqeSimplifyTrans e1                 e2          = EqeTrans e1 e2

eqeSimplifyCongAppend :: EqETerm -> EqETerm -> EqETerm
eqeSimplifyCongAppend (EqeRefl etn1) (EqeRefl _etn2) = EqeRefl etn1
eqeSimplifyCongAppend e1             e2              = EqeCongAppend e1 e2

eqeSimplify :: EqETerm -> EqETerm
eqeSimplify eqe = case eqe of
  EqeRefl etn                 -> EqeRefl etn
  EqeSym e                    -> eqeSimplifySym e
  EqeTrans e1 e2              -> eqeSimplifyTrans (eqeSimplify e1) (eqeSimplify e2)
  EqeCongAppend e1 e2         -> eqeSimplifyCongAppend (eqeSimplify e1) (eqeSimplify e2)
  EqeShiftAppend c et1 et2    -> EqeShiftAppend c et1 et2
  EqeSubstAppend x st et1 et2 -> EqeSubstAppend x st et1 et2

eqeSimplifySym :: EqETerm -> EqETerm
eqeSimplifySym eqe = case eqe of
  EqeRefl etn                 -> EqeRefl etn
  EqeSym e                    -> eqeSimplifySym e
  EqeTrans e1 e2              -> eqeSimplifyTrans (eqeSimplifySym e2) (eqeSimplifySym e1)
  EqeCongAppend e1 e2         -> eqeSimplifyCongAppend (eqeSimplifySym e1) (eqeSimplifySym e2)
  EqeShiftAppend c et1 et2    -> EqeSym (EqeShiftAppend c et1 et2)
  EqeSubstAppend x st et1 et2 -> EqeSym (EqeSubstAppend x st et1 et2)

evalScope :: EnvVariable -> BindSpec -> HVarlist
evalScope ev Nil         = HVDomainEnv (EVar ev)
evalScope ev (bs :. bsi) = HVAppend (evalScope ev bs) (evalBindSpecItem bsi)
