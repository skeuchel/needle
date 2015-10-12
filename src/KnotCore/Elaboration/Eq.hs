{-# LANGUAGE MultiParamTypeClasses #-}

module KnotCore.Elaboration.Eq where

import Coq.Syntax
import Coq.StdLib

import KnotCore.Syntax
import KnotCore.Elaboration.Core

data EqHVL
  = EqhRefl HVarlist
  | EqhShiftFun NamespaceTypeName FunName SubtreeVar
  | EqhSubstFun NamespaceTypeName FunName SubtreeVar
  | EqhCongAppend EqHVL EqHVL
  | EqhSym EqHVL
  | EqhTrans EqHVL EqHVL
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
  deriving (Eq,Ord,Show)

instance TypeNameOf EqTerm SortTypeName where
  typeNameOf (EqtRefl stn)          = stn
  typeNameOf (EqtAssumption stn _)  = stn
  typeNameOf (EqtCongWeaken eqt _)  = typeNameOf eqt
  typeNameOf (EqtCongShift _ eqt)   = typeNameOf eqt
  typeNameOf (EqtCongSubst _ _ eqt) = typeNameOf eqt
  typeNameOf (EqtSym eqt)           = typeNameOf eqt
  typeNameOf (EqtTrans eqt _)       = typeNameOf eqt

eqhvlEvalBindspecShift :: Elab m => NamespaceTypeName -> BindSpec -> m EqHVL
eqhvlEvalBindspecShift ntn bs =
  case bs of
    []       -> pure (EqhRefl HV0)
    (vli:bs) ->
       EqhCongAppend
       <$> case vli of
             VleBinding _ mv -> pure (EqhRefl (HVS (typeNameOf mv) HV0))
             VleCall ntns fn sv -> do
               deps <- getSortNamespaceDependencies (typeNameOf sv)
               if ntn `elem` deps
                 then pure $ EqhShiftFun ntn fn sv
                 else pure (EqhRefl (HVCall ntns fn (SVar sv)))
       <*> eqhvlEvalBindspecShift ntn bs

eqhvlEvalBindspecSubst :: Elab m => NamespaceTypeName -> BindSpec -> m EqHVL
eqhvlEvalBindspecSubst ntn bs =
  case bs of
    []       -> pure (EqhRefl HV0)
    (vli:bs) ->
       EqhCongAppend
       <$> case vli of
             VleBinding _ mv -> pure (EqhRefl (HVS (typeNameOf mv) HV0))
             VleCall ntns fn sv -> do
               deps <- getSortNamespaceDependencies (typeNameOf sv)
               if ntn `elem` deps
                 then pure $ EqhSubstFun ntn fn sv
                 else pure (EqhRefl (HVCall ntns fn (SVar sv)))
       <*> eqhvlEvalBindspecSubst ntn bs

instance TermLike EqHVL where
  toTerm (EqhRefl h)               = TermApp eqRefl
                                     <$> sequence [toTerm h]
  toTerm (EqhSym eqh)              = eqSym <$> toTerm eqh
  toTerm (EqhTrans eqh1 eqh2)      = eqTrans <$> toTerm eqh1 <*> toTerm eqh2
  toTerm (EqhCongAppend eqh1 eqh2) =
    eqFEqual2
    <$> (idAppendHVarlist >>= toRef)
    <*> toTerm eqh1 <*> toTerm eqh2
  toTerm (EqhShiftFun ntn fn _)    =
    TermApp
    <$> (idLemmaStabilityShift ntn fn >>= toRef)
    <*> pure [TermUnderscore,TermUnderscore]
  toTerm (EqhSubstFun ntn fn _)    =
    TermApp
    <$> (idLemmaStabilitySubst ntn fn >>= toRef)
    <*> pure [TermUnderscore,TermUnderscore,TermUnderscore]

instance TermLike EqCutoff where
  toTerm (EqcRefl _)               = pure eqRefl
  toTerm (EqcCongSucc eqc)       =
    eqFEqual
    <$> (idFamilyCutoffSucc >>= toRef)
    <*> toTerm eqc
  toTerm (EqcCongWeaken eqc eqh)   =
    eqFEqual2
    <$> (idFunctionWeakenCutoff (typeNameOf eqc) >>= toRef)
    <*> toTerm eqc  <*> toTerm eqh
  -- toTerm (EqcCongShift _ _)        = error "NOT IMPLEMENTED"
  -- toTerm (EqcCongShift' _ _)       = error "NOT IMPLEMENTED"
  -- toTerm (EqcWeakenShift _)        = error "NOT IMPLEMENTED"
  -- toTerm (EqcWeakenShift' _)       = error "NOT IMPLEMENTED"
  toTerm (EqcWeakenAppend c h1 h2) =
    TermApp
    <$> (idLemmaWeakenCutoffAppend (typeNameOf c) >>= toRef)
    <*> sequence [toTerm c, toTerm h1, toTerm h2]
  toTerm (EqcSym eqc)              = eqSym <$> toTerm eqc
  toTerm (EqcTrans eqc1 eqc2)      = eqTrans <$> toTerm eqc1 <*> toTerm eqc2

instance TermLike EqTrace where
  toTerm (EqxRefl _)             = pure eqRefl
  toTerm (EqxCongSucc _ eqx)       =
    eqFEqual
    <$> (idFamilyTraceCons >>= toRef)
    <*> toTerm eqx
  toTerm (EqxCongWeaken eqx eqh)   =
    eqFEqual2
    <$> (idFunctionWeakenTrace >>= toRef)
    <*> toTerm eqx  <*> toTerm eqh
  toTerm (EqxWeakenAppend x h1 h2) =
    TermApp
    <$> (idLemmaWeakenTraceAppend >>= toRef)
    <*> sequence
        [ toRef (typeNameOf x)
        , toTerm x
        , toTerm h1
        , toTerm h2
        ]
  toTerm (EqxSym eqx)              = eqSym <$> toTerm eqx
  toTerm (EqxTrans eqx1 eqx2)      = eqTrans <$> toTerm eqx1 <*> toTerm eqx2

instance TermLike EqTerm where
  toTerm (EqtRefl _)                = pure eqRefl
  toTerm (EqtAssumption _ tm)      = pure tm
  toTerm (EqtCongWeaken _ _)       = error "NOT IMPLEMENTED"
  toTerm (EqtCongShift eqc eqt)    =
    eqFEqual2
    <$> (idFunctionShift (typeNameOf eqc) (typeNameOf eqt) >>= toRef)
    <*> toTerm eqc  <*> toTerm eqt
  toTerm (EqtCongSubst eqx eqts eqtt)    =
    eqFEqual3
    <$> (idFunctionSubst (typeNameOf eqx) (typeNameOf eqtt) >>= toRef)
    <*> toTerm eqx <*> toTerm eqts <*> toTerm eqtt
  toTerm (EqtSym eqt)              = eqSym <$> toTerm eqt
  toTerm (EqtTrans eqt1 eqt2)      = eqTrans <$> toTerm eqt1 <*> toTerm eqt2

simplifyHvl :: HVarlist -> HVarlist
simplifyHvl HV0                = HV0
simplifyHvl (HVS ntn h)        = HVS ntn (simplifyHvl h)
simplifyHvl (HVVar hv)         = HVVar hv
simplifyHvl (HVCall ntn fn sv) = HVCall ntn fn sv
simplifyHvl (HVAppend h1 h2)   = simplifyHvlAppend (simplifyHvl h1) (simplifyHvl h2)
simplifyHvl (HVDomainEnv e)    = HVDomainEnv e

simplifyHvlAppend :: HVarlist -> HVarlist -> HVarlist
simplifyHvlAppend h1 HV0          = h1
simplifyHvlAppend h1 (HVS ntn h2) = HVS ntn (simplifyHvlAppend h1 h2)
simplifyHvlAppend h1 h2           = HVAppend h1 h2

simplifyCutoff :: Cutoff -> Cutoff
simplifyCutoff (C0 ntn)      = C0 ntn
simplifyCutoff (CS c)        = CS (simplifyCutoff c)
simplifyCutoff (CS' ntn c)   = let c' = simplifyCutoff c
                               in if typeNameOf c' == ntn
                                  then CS c else c
simplifyCutoff (CVar c)      = CVar c
simplifyCutoff (CWeaken c h) = simplifyCutoffWeaken c (simplifyHvl h)

simplifyCutoffWeaken :: Cutoff -> HVarlist -> Cutoff
simplifyCutoffWeaken c HV0         = simplifyCutoff c
simplifyCutoffWeaken c (HVS ntn h)
  | typeNameOf c == ntn = CS (simplifyCutoffWeaken c h)
  | otherwise           = simplifyCutoffWeaken c h
simplifyCutoffWeaken c h           = CWeaken (simplifyCutoff c) h


simplifyTrace :: Trace -> Trace
simplifyTrace (T0 ntn)      = T0 ntn
simplifyTrace (TS ntnb c)   = TS ntnb (simplifyTrace c)
simplifyTrace (TVar x)      = TVar x
simplifyTrace (TWeaken x h) = simplifyTraceWeaken x (simplifyHvl h)

simplifyTraceWeaken :: Trace -> HVarlist -> Trace
simplifyTraceWeaken x HV0         = simplifyTrace x
-- simplifyTraceWeaken x (HVS ntn h)
--   | typeNameOf x == ntn = TS (simplifyTraceWeaken x h)
--   | otherwise           = simplifyTraceWeaken x h
simplifyTraceWeaken x h           = TWeaken (simplifyTrace x) h

{-
   ___      _  ___   ___
  | __|__ _| || \ \ / / |
  | _|/ _` | __ |\ V /| |__
  |___\__, |_||_| \_/ |____|
         |_|
-}

eqhSimplifyTrans :: EqHVL -> EqHVL -> EqHVL
eqhSimplifyTrans (EqhRefl _)        e2          = e2
eqhSimplifyTrans e1                 (EqhRefl _) = e1
eqhSimplifyTrans (EqhTrans e11 e12) e2          = eqhSimplifyTrans e11 (eqhSimplifyTrans e12 e2)
eqhSimplifyTrans e1                 e2          = EqhTrans e1 e2

eqhSimplifyCongAppend :: EqHVL -> EqHVL -> EqHVL
eqhSimplifyCongAppend (EqhRefl h1) (EqhRefl h2) = EqhRefl (HVAppend h1 h2)
eqhSimplifyCongAppend e1           e2           = EqhCongAppend e1 e2

eqhSimplify :: EqHVL -> EqHVL
eqhSimplify eqh =
  case eqh of
    EqhRefl h             -> EqhRefl (simplifyHvl h)
    EqhSym e              -> eqhSimplifySym e
    EqhTrans e1 e2        -> eqhSimplifyTrans (eqhSimplify e1) (eqhSimplify e2)
    EqhCongAppend e1 e2   -> eqhSimplifyCongAppend (eqhSimplify e1) (eqhSimplify e2)
    EqhShiftFun ntn fn sv -> EqhShiftFun ntn fn sv
    EqhSubstFun ntn fn sv -> EqhSubstFun ntn fn sv

eqhSimplifySym :: EqHVL -> EqHVL
eqhSimplifySym eqh =
  case eqh of
    EqhRefl h             -> EqhRefl (simplifyHvl h)
    EqhSym e              -> eqhSimplify e
    EqhTrans e1 e2        -> eqhSimplifyTrans (eqhSimplifySym e2) (eqhSimplifySym e1)
    EqhCongAppend e1 e2   -> eqhSimplifyCongAppend (eqhSimplifySym e1) (eqhSimplifySym e2)
    EqhShiftFun ntn fn sv -> EqhSym (EqhShiftFun ntn fn sv)
    EqhSubstFun ntn fn sv -> EqhSym (EqhSubstFun ntn fn sv)

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
