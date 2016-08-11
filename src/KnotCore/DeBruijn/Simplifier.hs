{-# LANGUAGE GADTs #-}

module KnotCore.DeBruijn.Simplifier where

import KnotCore.DeBruijn.Core
import KnotCore.Syntax

simplifyHvl :: HVarlist -> HVarlist
simplifyHvl HV0                = HV0
simplifyHvl (HVS ntn h)        = HVS ntn (simplifyHvl h)
simplifyHvl (HVVar hv)         = HVVar hv
simplifyHvl (HVCall fn sv)     = HVCall fn sv
simplifyHvl (HVAppend h1 h2)   = simplifyHvlAppend (simplifyHvl h1) (simplifyHvl h2)
simplifyHvl (HVDomainEnv et)   = simplifyHvlDomain et

simplifyHvlAppend :: HVarlist -> HVarlist -> HVarlist
simplifyHvlAppend h1 HV0          = h1
simplifyHvlAppend h1 (HVS ntn h2) = HVS ntn (simplifyHvlAppend h1 h2)
simplifyHvlAppend h1 h2           = HVAppend h1 h2

simplifyHvlDomain :: ETerm -> HVarlist
simplifyHvlDomain (ENil _)            = HV0
simplifyHvlDomain (ECons et ntn _sts) = HVS ntn (simplifyHvlDomain et)
simplifyHvlDomain et                  = HVDomainEnv et

--------------------------------------------------------------------------------

simplifyIndex :: Index -> Index
simplifyIndex (I0 ntn stn) = I0 ntn stn
simplifyIndex (IS i) = IS (simplifyIndex i)
simplifyIndex (IVar iv) = IVar iv
simplifyIndex (IWeaken i hvl) = simplifyIndexWeaken (simplifyIndex i) (simplifyHvl hvl)
simplifyIndex (IShift c i) = IShift (simplifyCutoff c) (simplifyIndex i)
simplifyIndex (IShift' c i) = IShift' (simplifyCutoff c) (simplifyIndex i)

simplifyIndexWeaken :: Index -> HVarlist -> Index
simplifyIndexWeaken i HV0 = i
simplifyIndexWeaken i (HVS ntn h)
  | typeNameOf i == ntn = IS (simplifyIndexWeaken i h)
  | otherwise           = simplifyIndexWeaken i h
simplifyIndexWeaken i h = IWeaken i h

--------------------------------------------------------------------------------
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

--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------

simplifyETerm :: ETerm -> ETerm
simplifyETerm et' = case et' of
  EVar ev          -> EVar ev
  ENil etn         -> ENil etn
  ECons et ntn sts -> ECons (simplifyETerm et) ntn sts
  EAppend et1 et2  -> simplifyEAppend (simplifyETerm et1) (simplifyETerm et2)
  EShift c et      -> simplifyEShift c (simplifyETerm et)
  EShift' c et     -> simplifyEShift' c (simplifyETerm et)
  ESubst x st et   -> simplifyESubst x st (simplifyETerm et)
  ESubst' x st et  -> simplifyESubst' x st (simplifyETerm et)
  EWeaken et h     -> simplifyEWeaken (simplifyETerm et) (simplifyHvl h)

simplifyEAppend :: ETerm -> ETerm -> ETerm
simplifyEAppend et1 (ENil _)            = et1
simplifyEAppend et1 (ECons et2 ntn sts) = ECons (simplifyEAppend et1 et2) ntn sts
simplifyEAppend et1 et2                 = EAppend et1 et2

simplifyEWeaken :: ETerm -> HVarlist -> ETerm
simplifyEWeaken et HV0 = et
simplifyEWeaken et h   = EWeaken et h

simplifyShiftField :: Cutoff -> Field w -> Field w
simplifyShiftField c f = case f of
  FieldSort st -> FieldSort (SShift' c st)
  FieldEnv et  -> FieldEnv (EShift' c et)
  FieldIndex i -> FieldIndex (IShift' c i)

simplifyEShift :: Cutoff -> ETerm -> ETerm
simplifyEShift _c (ENil etn)         = ENil etn
simplifyEShift c (ECons et ntn sfs) =
  ECons
    (simplifyEShift c et)
    ntn
    (map (simplifyShiftField (CWeaken c (HVDomainEnv et))) sfs)
simplifyEShift c et                 = EShift c et

simplifyEShift' :: Cutoff -> ETerm -> ETerm
simplifyEShift' _c (ENil etn) = ENil etn
simplifyEShift' c (ECons et ntn sfs) =
  ECons (simplifyEShift' c et) ntn (map (simplifyShiftField (CWeaken c (HVDomainEnv et))) sfs)
simplifyEShift' c et         = EShift' c et

simplifyESubst :: Trace -> STerm -> ETerm -> ETerm
simplifyESubst x st et = case et of
  ENil etn -> ENil etn
  _        -> ESubst x st et

simplifyESubst' :: Trace -> STerm -> ETerm -> ETerm
simplifyESubst' x st et = case et of
  ENil etn -> ENil etn
  _        -> ESubst' x st et
