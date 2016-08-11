{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module KnotCore.Elaboration.Core (
  module KnotCore.Elaboration.Core, module REEXPORT
) where

import           Knot.Env as REEXPORT
import           Knot.Fresh as REEXPORT

import           KnotCore.DeBruijn.Core as REEXPORT
import           KnotCore.DeBruijn.Eq as REEXPORT
import           KnotCore.DeBruijn.Simplifier as REEXPORT
import           KnotCore.Elaboration.Fresh as REEXPORT
import           KnotCore.Elaboration.Identifiers as REEXPORT
import           KnotCore.Elaboration.Monad as REEXPORT
import           KnotCore.Environment as REEXPORT
import           KnotCore.Syntax as REEXPORT

import qualified Coq.StdLib as Coq
import qualified Coq.Syntax as Coq


import           Control.Monad
import           Data.Maybe
import           Data.Traversable (Traversable(..))

class Ident a => Variable a where
  toBinder :: Elab m => a -> m Coq.Binder
  toImplicitBinder :: Elab m => a -> m Coq.Binder
  toImplicitBinder a = do
    b <- toBinder a
    return $ case b of
      Coq.BinderName nm         -> Coq.BinderImplicitName nm
      Coq.BinderNameType nms tm -> Coq.BinderImplicitNameType nms tm
      _                         -> b

class Idents a where
  toIds     :: Elab m => a -> m [Coq.Identifier]
  toQualIds :: Elab m => a -> m [Coq.QualId]
  toQualIds = fmap (map Coq.Ident) . toIds
  toNames   :: Elab m => a -> m [Coq.Name]
  toNames = fmap (map Coq.NameIdent) . toIds
  toRefs    :: Elab m => a -> m [Coq.Term]
  toRefs = fmap (map Coq.TermQualId) . toQualIds

instance Ident IndexVar where
  toId (IndexVar nr suff _ _) = return $ Coq.ID (nrId nr ++ suff)
instance Variable IndexVar where
  toBinder index =
    Coq.BinderNameType
    <$> sequenceA [ toName index ]
    <*> typeIndex (typeNameOf index)

instance Ident HVarlistVar where
  toId tv = return . Coq.ID $
              nrId (hvarlistVarRoot tv) ++
              hvarlistVarSuffix tv
instance Variable HVarlistVar where
  toBinder trace =
    Coq.BinderNameType
    <$> sequenceA [ toName trace ]
    <*> (idTypeHVarlist >>= toRef)

instance Ident CutoffVar where
  toId cv = return . Coq.ID $
              nrId (cutoffVarRoot cv) ++
              cutoffVarSuffix cv
instance Variable CutoffVar where
  toBinder cutoff =
    Coq.BinderNameType
    <$> sequenceA [ toName cutoff ]
    <*> typeCutoff (typeNameOf cutoff)

instance Ident TermVar where
  toId (TermVar nr suff _) =
    return $ Coq.ID (nrId nr ++ suff)

instance Ident SortVariable where
  toId (SV nr suff _) =
    return $ Coq.ID (nrId nr ++ suff)
instance Variable SortVariable where
  toBinder sv =
    Coq.BinderNameType
    <$> sequenceA [ toName sv ]
    <*> toRef (typeNameOf sv)

instance Ident TraceVar where
  toId tv = return . Coq.ID $
              nrId (traceVarRoot tv) ++
              traceVarSuffix tv
instance Variable TraceVar where
  toBinder trace =
    Coq.BinderNameType
    <$> sequenceA [ toName trace ]
    <*> typeTrace (typeNameOf trace)

instance Ident EnvVariable where
  toId envVar =
    return . Coq.ID $
      nrId (evRoot envVar) ++
      evSuffix envVar
instance Variable EnvVariable where
  toBinder envVar =
    Coq.BinderNameType
    <$> sequenceA [ toName envVar ]
    <*> toRef (typeNameOf envVar)

instance Ident LookupVar where
  toId (LookupVar nr suff _ _ _) = return $ Coq.ID (nrId nr ++ suff)
instance Variable LookupVar where
  toBinder lkv@(LookupVar _ _ se rv sfs) = do
    et   <- symbolicEnvToETerm se
    i    <- toIndex rv
    sfs' <- catMaybes <$> traverse symbolicFieldToField sfs
    Coq.BinderNameType
      <$> sequenceA [ toName lkv ]
      <*> toTerm (Lookup et (IVar i) sfs')

instance Ident JudgementVariable where
  toId (JV nr suff _rtn) = return $ Coq.ID (nrId nr ++ suff)

jvBinder :: Elab m => JudgementVariable -> Judgement -> m Coq.Binder
jvBinder jmv (Judgement rtn mbSe sfs outs) = do
  jmenv <- case mbSe of
             Just se -> JudgementEnvTerm <$> symbolicEnvToETerm se
             Nothing -> pure JudgementEnvNothing
  sfs' <- catMaybes <$> traverse symbolicFieldToField sfs
  outs' <- traverse (symbolicEnvToETerm.snd) outs
  Coq.BinderNameType
    <$> sequenceA [ toName jmv ]
    <*> toTerm (PJudgement rtn jmenv sfs' outs')

instance Ident InsertEnvHyp where
  toId (InsertEnvHyp hyp _) = toId hyp
instance Variable InsertEnvHyp where
  toBinder (InsertEnvHyp hyp ins) =
    Coq.BinderNameType
      <$> sequenceA [ toName hyp ]
      <*> toTerm ins

instance Ident SubstEnvHyp where
  toId (SubstEnvHyp hyp _) = toId hyp
instance Variable SubstEnvHyp where
  toBinder (SubstEnvHyp hyp sub) =
    Coq.BinderNameType
      <$> sequenceA [ toName hyp ]
      <*> toTerm sub

instance Ident Hypothesis where
  toId (Hypothesis nr suff) = return $ Coq.ID (nrId nr ++ suff)
instance Variable Hypothesis where
  toBinder ih = Coq.BinderName <$> toName ih

-- Coq identifiers
instance Ident Coq.Variable where
  toId (Coq.Variable ident _) = toId ident
instance Variable Coq.Variable where
  toBinder (Coq.Variable ident tm) =
    Coq.BinderNameType
    <$> sequenceA [toName ident]
    <*> pure tm

instance Ident WellFormedSortHyp where
  toId (WellFormedSortHyp hyp _) = toId hyp
instance Variable WellFormedSortHyp where
  toBinder (WellFormedSortHyp hyp wfs) =
    Coq.BinderNameType <$> sequenceA [toName hyp] <*> toTerm wfs
instance Ident WellFormedIndexHyp where
  toId (WellFormedIndexHyp hyp _) = toId hyp
instance Variable WellFormedIndexHyp where
  toBinder (WellFormedIndexHyp hyp wfi) =
    Coq.BinderNameType <$> sequenceA [toName hyp] <*> toTerm wfi

instance Ident WellFormedHyp where
  toId (WellFormedHypSort hyp) = toId hyp
  toId (WellFormedHypIndex hyp) = toId hyp
instance Variable WellFormedHyp where
  toBinder (WellFormedHypSort hyp) = toBinder hyp
  toBinder (WellFormedHypIndex hyp) = toBinder hyp

--    _           _ _ _
--   /_\ _  ___ _(_) (_)__ _ _ _ _  _
--  / _ \ || \ \ / | | / _` | '_| || |
-- /_/ \_\_,_/_\_\_|_|_\__,_|_|  \_, |
--                               |__/

-- TODO: get rid of this and it's clients. use specialized code instead.
freshVariable :: Elab m => String -> Coq.Term -> m Coq.Variable
freshVariable nr tm = do
  suff <- freshenSuffix (NR LocNoWhere nr) ""
  return (Coq.Variable (Coq.ID $ nr ++ suff) tm)

class TermLike a where
  toTerm      :: Elab m => a -> m Coq.Term
  toTerm = toTermInt
  toTermInt   :: Elab m => a -> m Coq.Term
  toMatchItem :: Elab m => a -> m Coq.Term
  toMatchItem = toTerm

instance TermLike HVarlist where
  toTerm = toTermInt . simplifyHvl
  toTermInt (HV0)                 = idCtorHVarlistNil >>= toRef
  toTermInt (HVS ntn hvl)         = Coq.TermApp
                                    <$> (idCtorHVarlistCons >>= toRef)
                                    <*> sequenceA [idCtorNamespace ntn >>= toRef, toTermInt hvl]
  toTermInt (HVVar hvv)           = toRef hvv
  toTermInt (HVCall fn sn)        = Coq.TermApp
                                    <$> toRef fn
                                    <*> sequenceA [toTermInt sn]
  toTermInt (HVAppend hvl1 hvl2)  = Coq.TermApp
                                    <$> (idAppendHVarlist >>= toRef)
                                    <*> sequenceA [toTermInt hvl1, toTermInt hvl2]
  toTermInt (HVDomainEnv et)      = Coq.TermApp
                                    <$> (idFunctionDomainEnv (typeNameOf et) >>= toRef)
                                    <*> sequenceA [toTermInt et]

instance TermLike Cutoff where
  toTerm = toTermInt . simplifyCutoff
  toTermInt (C0 _)                = idFamilyCutoffZero >>= toRef
  toTermInt (CS c)                = Coq.TermApp
                                    <$> (idFamilyCutoffSucc >>= toRef)
                                    <*> sequenceA [toTermInt c]
  toTermInt (CS' ntn c)           = if typeNameOf c == ntn
                                    then toTermInt (CS c)
                                    else toTermInt c
  toTermInt (CVar cv)             = toRef cv
  toTermInt (CWeaken c hvl)       = Coq.TermApp
                                    <$> (idFunctionWeakenCutoff (typeNameOf c) >>= toRef)
                                    <*> sequenceA [toTerm c, toTerm hvl]

instance TermLike Index where
  toTerm = toTermInt . simplifyIndex
  toTermInt (I0 _ _)              = idFamilyIndexZero >>= toRef
  toTermInt (IS i)                = Coq.TermApp
                                    <$> (idFamilyIndexSucc >>= toRef)
                                    <*> sequenceA [toTermInt i]
  toTermInt (IVar iv)             = toRef iv
  toTermInt (IShift c i)          = Coq.TermApp
                                    <$> (idFunctionShiftIndex (typeNameOf c) >>= toRef)
                                    <*> sequenceA [toTerm c, toTermInt i]
  toTermInt (IShift' c i)         = if typeNameOf c == typeNameOf i
                                    then toTermInt (IShift c i)
                                    else toTermInt i
  toTermInt (IWeaken i hvl)       = Coq.TermApp
                                    <$> (idFunctionWeakenIndex (typeNameOf i) >>= toRef)
                                    <*> sequenceA [toTermInt i, toTerm hvl]

instance TermLike Trace where
  toTermInt (T0 _)                = idFamilyTraceNil >>= toRef
  toTermInt (TS ntn c)            = Coq.TermApp
                                    <$> (idFamilyTraceCons >>= toRef)
                                    <*> sequenceA [toRef ntn, toTerm c]
  toTermInt (TVar cv)             = toRef cv
  toTermInt (TWeaken c hvl)       = Coq.TermApp
                                    <$> (idFunctionWeakenTrace >>= toRef)
                                    <*> sequenceA [toTermInt c, toTerm hvl]

instance TermLike (Field w) where
  toTermInt (FieldSort st)        = toTermInt st

instance TermLike STerm where
  toTermInt (SVar sv)             = toRef sv
  toTermInt (SCtorVar _stn cn i)  = Coq.TermApp
                                    <$> toRef cn
                                    <*> sequenceA [toTerm i]
  toTermInt (SCtorReg _stn cn ss) = Coq.TermApp
                                    <$> toRef cn
                                    <*> traverse toTerm ss
  toTermInt (SShift c t)          = Coq.TermApp
                                    <$> (idFunctionShift (typeNameOf c) (typeNameOf t) >>= toRef)
                                    <*> sequenceA [toTerm c, toTerm t]
  toTermInt (SShift' c t)         = do
                                      deps <- getSortNamespaceDependencies (typeNameOf t)
                                      if typeNameOf c `elem` deps
                                        then toTerm (SShift c t)
                                        else toTerm t
  toTermInt (SSubst x s t)        = Coq.TermApp
                                    <$> (idFunctionSubst (typeNameOf x) (typeNameOf t) >>= toRef)
                                    <*> sequenceA [toTerm x, toTerm s, toTerm t]
  toTermInt (SSubst' x s t)       = do
                                      deps <- getSortNamespaceDependencies (typeNameOf t)
                                      if typeNameOf x `elem` deps
                                      then toTerm (SSubst x s t)
                                      else toTerm t
  toTermInt (SSubstIndex x s y)   = Coq.TermApp
                                    <$> (idFunctionSubstIndex (typeNameOf y) >>= toRef)
                                    <*> sequenceA [toTerm x, toTerm s, toTerm y]
  toTermInt (SWeaken t hvl)       = Coq.TermApp
                                    <$> (idFunctionWeakenTerm (typeNameOf t) >>= toRef)
                                    <*> sequenceA [toTerm t, toTerm hvl]

instance TermLike ETerm where
  toTerm = toTermInt . simplifyETerm
  toTermInt (EVar ev)             = toRef ev
  toTermInt (ENil etn)            = getEnvCtorNil etn >>= toRef
  toTermInt (ECons et ntn ts)     = do
                                      (_,cn) <- getNamespaceEnvCtor ntn
                                      Coq.TermApp
                                        <$> toRef cn
                                        <*> sequenceA (toTerm et : map toTerm ts)
  toTermInt (EAppend et1 et2)     = Coq.TermApp
                                    <$> (idFunctionAppendEnv (typeNameOf et1) >>= toRef)
                                    <*> sequenceA [toTerm et1, toTerm et2]
  toTermInt (EShift c et)         = Coq.TermApp
                                    <$> (idFunctionShiftEnv (typeNameOf c) (typeNameOf et) >>= toRef)
                                    <*> sequenceA [toTerm c, toTerm et]
  toTermInt (EShift' c et)        = do
                                      deps <- getEnvNamespaceDependencies (typeNameOf et)
                                      if typeNameOf c `elem` deps
                                        then toTerm (EShift c et)
                                        else toTerm et
  toTermInt (ESubst x s et)       = Coq.TermApp
                                    <$> (idFunctionSubstEnv (typeNameOf x) (typeNameOf et) >>= toRef)
                                    <*> sequenceA [toTerm x, toTerm s, toTerm et]
  toTermInt (ESubst' x s et)      = do
                                      deps <- getEnvNamespaceDependencies (typeNameOf et)
                                      if typeNameOf x `elem` deps
                                        then toTerm (ESubst x s et)
                                        else toTerm et
  toTermInt (EWeaken et hvl)      = Coq.TermApp
                                    <$> (idFunctionWeakenEnv (typeNameOf et) >>= toRef)
                                    <*> sequenceA [toTerm et, toTerm hvl]

instance TermLike Lookup where
  toTermInt (Lookup et x ts) = do
    cn <- getEnvCtorName (typeNameOf et) (typeNameOf x)
    typeLookup cn et x ts

instance TermLike InsertEnv where
  toTermInt (InsertEnv c et1 et2) = do
    cn <- getEnvCtorName (typeNameOf et1) (typeNameOf c)
    typeInsertEnv cn c et1 et2

instance TermLike InsertEnvTerm where
  toTermInt (InsertEnvVar hyp) = toRef hyp
  toTermInt (InsertEnvCons thereNtn sts iet) = do
    let (insNtn,etn) = typeNameOf iet
    thereCn <- getEnvCtorName etn thereNtn
    insCn   <- getEnvCtorName etn insNtn
    cn      <- idCtorInsertEnvThere insCn thereCn
    Coq.TermApp
      <$> toRef cn
      <*> sequenceA (toTerm iet : map toTerm sts)
  toTermInt (InsertEnvWeaken iet et) = do
    let (insNtn,etn) = typeNameOf iet
    insCn   <- getEnvCtorName etn insNtn
    Coq.TermApp
      <$> (idLemmaWeakenInsertEnv insCn >>= toRef)
      <*> sequenceA [toTerm et, toTerm iet]

instance TermLike SubstEnvTerm where
  toTermInt (SubstEnvVar hyp) = toRef hyp
  toTermInt (SubstEnvCons thereNtn sts iet) = do
    let (subNtn,etn) = typeNameOf iet
    thereCn <- getEnvCtorName etn thereNtn
    subCn   <- getEnvCtorName etn subNtn
    cn      <- idCtorSubstEnvThere subCn thereCn
    Coq.TermApp
      <$> toRef cn
      <*> sequenceA (toTerm iet : map toTerm sts)
  toTermInt (SubstEnvWeaken iet et) = do
    let (subNtn,etn) = typeNameOf iet
    (ftns,_) <- lookupEnvClause etn subNtn
    subCn   <- getEnvCtorName etn subNtn
    Coq.TermApp
      <$> (idLemmaWeakenSubstEnv subCn >>= toRef)
      <*> sequenceA (map (const (pure Coq.underscore)) ftns ++ [toTerm et, toTerm iet])

instance TermLike SubstEnv where
  toTermInt (SubstEnv e fs t x e1 e2) = do
    cn <- getEnvCtorName (typeNameOf e) (typeNameOf x)
    typeSubstEnv cn e fs t x e1 e2
  toMatchItem (SubstEnv e fs t x e1 e2) = do
    cn <- getEnvCtorName (typeNameOf e) (typeNameOf x)
    Coq.TermApp
      <$> (idTypeSubstEnv cn >>= toRef)
      <*> (sequenceA $ concat
           [ [ pure Coq.underscore ]
           , map (const (pure Coq.underscore)) fs
           , [ pure Coq.underscore
             , toTerm x
             , toTerm e1
             , toTerm e2
             ]
           ]
          )

instance TermLike Prop where
  toTermInt (PEqTerm l r)            = Coq.TermEq <$> toTerm l <*> toTerm r
  toTermInt (PEqField l r)           = Coq.TermEq <$> toTerm l <*> toTerm r
  toTermInt (PAnd ps)                = Coq.TermAnd <$> traverse toTerm ps
  toTermInt (PJudgement rtn mbE sts ses) =
    Coq.TermApp
    <$> toRef rtn
    <*> (concat <$> sequenceA
           [ case mbE of
               JudgementEnvTerm et     -> sequenceA [toTerm et]
               JudgementEnvUnderscore  -> pure [Coq.TermUnderscore]
               JudgementEnvNothing     -> pure []
           , traverse toTerm sts
           , traverse toTerm ses
           ]
        )
  toTermInt (PEqHvl h1 h2) = Coq.TermEq <$> toTerm h1 <*> toTerm h2

instance TermLike WellFormedIndex where
  toTermInt (WfIndex h i) = Coq.TermApp
                         <$> (idFunctionWellFormedIndex >>= toRef)
                         <*> sequenceA [toTerm h, toTerm i]

instance TermLike WellFormedSort where
  toTermInt (WfSort h s) =
    Coq.TermApp
    <$> (idRelationWellFormed (sortOf s) >>= toRef)
    <*> sequenceA [toTerm h, toTerm s]
  toMatchItem (WfSort _h s)  =
    Coq.TermApp
    <$> (idRelationWellFormed (sortOf s) >>= toRef)
    <*> sequenceA [pure Coq.underscore, toTerm s]

instance TermLike HVarlistInsertion where
  toTermInt (HVarlistInsertion c h1 h2) =
    Coq.TermApp
    <$> (idRelationHVarlistInsert (typeNameOf c) >>= toRef)
    <*> sequenceA [toTerm c, toTerm h1, toTerm h2]

instance TermLike SubstHvl where
  toTermInt (SubstHvl h x h1 h2) =
    Coq.TermApp
    <$> (idTypeSubstHvl (typeNameOf x) >>= toRef)
    <*> sequenceA [toTerm h, toTerm x, toTerm h1, toTerm h2]

instance TermLike SubHvl where
  toTermInt (SubHvl ntns h) =
    Coq.TermApp
    <$> (idFunctionSubHvl ntns >>= toRef)
    <*> sequenceA [toTerm h ]

instance TermLike InsertHvlTerm where
  toTermInt (InsertHvlEnv ins)      =
    Coq.TermApp
    <$> (uncurry (flip idLemmaInsertEnvInsertHvl) (typeNameOf ins) >>= toRef)
    <*> sequenceA [toTerm ins]
  toTermInt (InsertHvlWeaken rec hvl) =
    Coq.TermApp
    <$> (idLemmaWeakenRelationHVarlistInsert (typeNameOf rec) >>= toRef)
    <*> sequenceA [toTerm hvl, toTerm rec]

instance TermLike SubstHvlTerm where
  toTermInt (SubstHvlEnv sub)      = do
    let (ntn,etn) = typeNameOf sub
    (ftns,_) <- lookupEnvClause etn ntn
    Coq.TermApp
      <$> (uncurry (flip idLemmaSubstEnvSubstHvl) (typeNameOf sub) >>= toRef)
      <*> sequenceA
          (map (const (pure Coq.TermUnderscore)) ftns ++ [toTerm sub])
  toTermInt (SubstHvlWeaken rec hvl) =
    Coq.TermApp
    <$> (idLemmaWeakenSubstHvl (typeNameOf rec) >>= toRef)
    <*> sequenceA [toTerm hvl, toTerm rec]

instance TermLike WellFormedIndexHyp where
  toTermInt (WellFormedIndexHyp hyp _) = toRef hyp

instance TermLike WellFormedIndexTerm where
  toTermInt (WellFormedIndexVar hyp) = toTerm hyp
  toTermInt (WellFormedIndexShift ins wfi) =
    Coq.TermApp
    <$> (idLemmaShiftWellFormedIndex (typeNameOf ins) (typeNameOf wfi) >>= toRef)
    <*> sequenceA
        -- TODO: Fill in these underscores
        [ pure Coq.TermUnderscore
        , pure Coq.TermUnderscore
        , pure Coq.TermUnderscore
        , toTerm ins
        , pure Coq.TermUnderscore
        , toTerm wfi
        ]
  toTermInt (WellFormedIndexSubst subWf sub wfi) =

    Coq.TermApp
    <$> (idLemmaSubstHvlWfIndex (typeNameOf sub) (typeNameOf wfi) >>= toRef)
    <*> sequenceA
        (concat
          [ [ toTerm subWf | typeNameOf sub == typeNameOf wfi ]
          , [ toTerm sub
            , toTerm wfi
            ]
          ]
        )

instance TermLike WellFormedSortHyp where
  toTermInt (WellFormedSortHyp hyp _) = toRef hyp

instance TermLike WellFormedSortTerm where
  toTermInt (WellFormedSortVar hyp) = toTerm hyp
  toTermInt (WellFormedSortShift ins wft) =
    Coq.TermApp
    <$> (idLemmaShiftWellFormedSort (typeNameOf ins) (typeNameOf wft) >>= toRef)
    <*> sequenceA
        -- TODO: Fill in these underscores
        [ pure Coq.TermUnderscore
        , pure Coq.TermUnderscore
        , toTerm wft
        , pure Coq.TermUnderscore
        , pure Coq.TermUnderscore
        , toTerm ins
        ]
  toTermInt (WellFormedSortSubst subWf substEnv wft) = do
    deps  <- getSortNamespaceDependencies (typeNameOf wft)

    Coq.TermApp
      <$> (idLemmaSubstWellFormedSort (typeNameOf substEnv) (typeNameOf wft) >>= toRef)
      <*> sequenceA
          (concat
           [ [ toTermInt subWf | typeNameOf substEnv `elem` deps
             ]
           ,  -- TODO: Fill in these underscores
             [ pure Coq.TermUnderscore
             , pure Coq.TermUnderscore
             , toTerm wft
             , toTerm substEnv
             ]
           ]
          )
  toTermInt (WellFormedSortJudgement i stn jmv rtn jmEnv fs ets) =
    Coq.TermApp
    <$> (idLemmaRelationWellFormed rtn i >>= toRef)
    <*> sequenceA
        (concat
         [ [ toTerm jmEnv ]
         , map toTerm fs
         , map toTerm ets
         , [ toRef jmv ]
         ]
        )

typeLookup :: Elab m => CtorName -> ETerm -> Index -> [Field 'WOMV] -> m Coq.Term
typeLookup cn e x fs =
  Coq.TermApp
  <$> (idTypeLookup cn >>= toRef)
  <*> sequenceA (toTerm e:toTerm x:map toTerm fs)

typeInsertEnv :: Elab m => CtorName -> Cutoff -> ETerm -> ETerm -> m Coq.Term
typeInsertEnv cn c e1 e2 =
  Coq.TermApp
  <$> (idTypeInsertEnv cn >>= toRef)
  <*> sequenceA [toTerm c, toTerm e1, toTerm e2]

typeSubstEnv :: Elab m => CtorName -> ETerm -> [Field 'WOMV] -> STerm -> Trace -> ETerm -> ETerm -> m Coq.Term
typeSubstEnv cn e fs t x e1 e2 =
  Coq.TermApp
  <$> (idTypeSubstEnv cn >>= toRef)
  <*> sequenceA
        ([toTerm e] ++
         map toTerm fs ++
         [toTerm t, toTerm x, toTerm e1, toTerm e2]
        )

-- Subtree names
shiftedSubtreeRef :: Elab m => CutoffVar -> SortVariable -> m Coq.Term
shiftedSubtreeRef cv sv = do
  let ntn = typeNameOf cv
  deps  <- getSortNamespaceDependencies (typeNameOf sv)
  shift <- idFunctionShift ntn (typeNameOf sv)

  if ntn `elem` deps
    then Coq.TermApp <$> toRef shift <*> sequenceA [toRef cv, toRef sv]
    else toRef sv

-- Environment type names
nameEnvNil :: Elab m => EnvTypeName -> m Coq.Identifier
nameEnvNil etn = return (Coq.ID $ etnId etn ++ "_nil")

-- Hypothesis
hypothesisIdentifier :: Elab m => Hypothesis -> m Coq.Identifier
hypothesisIdentifier (Hypothesis nr suff) =
  return (Coq.ID $ nrId nr ++ suff)

hypothesisRef :: Elab m => Hypothesis -> m Coq.Term
hypothesisRef = fmap (Coq.TermQualId . Coq.Ident) . hypothesisIdentifier

eSymbolicTerm :: Elab m => SymbolicTerm -> m Coq.Term
eSymbolicTerm = symbolicTermToSTerm >=> toTerm

eSymbolicEnv :: Elab m => SymbolicEnv -> m Coq.Term
eSymbolicEnv = symbolicEnvToETerm >=> toTerm

eRuleMetavarBinder :: Elab m => RuleMetavarBinder -> m (Maybe Coq.Binder)
eRuleMetavarBinder rmb
  | RuleMetavarSort _ sv _ _ <- rmb
  = Just <$> toBinder sv
  | RuleMetavarFree fv _ <- rmb
  = Just <$> (toIndex fv >>= toBinder)
  | RuleMetavarOutput _ ev <- rmb
  = Just <$> toBinder ev
  | RuleMetavarBinding _ _ <- rmb
  = pure Nothing

eRuleMetavarId :: Elab m => RuleMetavarBinder -> m (Maybe Coq.Identifier)
eRuleMetavarId rmb
  | RuleMetavarSort _ sv _ _ <- rmb
  = Just <$> toId sv
  | RuleMetavarFree fv _ <- rmb
  = Just <$> (toIndex fv >>= toId)
  | RuleMetavarOutput _ ev <- rmb
  = Just <$> toId ev
  | RuleMetavarBinding _ _ <- rmb
  = pure Nothing

eRuleMetavarWellFormed :: Elab m =>
  Maybe EnvVariable -> RuleMetavarBinder -> m (Maybe (BindSpec, WellFormedHyp))
eRuleMetavarWellFormed mbEv (RuleMetavarSort bs sv hyp Nothing) = do
  let hvl = simplifyHvl $
              HVAppend (maybe HV0 (HVDomainEnv . EVar) mbEv) (evalBindSpec HV0 bs)
  wfs <- WellFormedSortHyp hyp
         <$> (WfSort <$> pure hvl <*> pure (SVar sv))
  pure (Just (bs, WellFormedHypSort wfs))
eRuleMetavarWellFormed _ (RuleMetavarSort _ _ _ (Just _)) =
  pure Nothing
eRuleMetavarWellFormed mbEv (RuleMetavarFree fv hyp) = do
  let hvl = maybe HV0 (HVDomainEnv . EVar) mbEv
  wfi <- WellFormedIndexHyp hyp
         <$> (WfIndex <$> pure hvl <*> (IVar <$> toIndex fv))
  pure (Just (Nil, WellFormedHypIndex wfi))
eRuleMetavarWellFormed _ (RuleMetavarOutput{}) = pure Nothing
eRuleMetavarWellFormed _ (RuleMetavarBinding{}) = pure Nothing

eFormulaId :: Elab m => Formula -> m Coq.Identifier
eFormulaId (FormLookup lkv _ _ _)    = toId lkv
eFormulaId (FormJudgement jmv _ _ _) = toId jmv

eFieldDeclBinders :: Elab m => [FieldDecl w] -> [m Coq.Binder]
eFieldDeclBinders = mapMaybe eFieldDeclBinder

eFieldDeclBinder :: Elab m => FieldDecl w -> Maybe (m Coq.Binder)
eFieldDeclBinder (FieldDeclSort _bs sv _svWf)  = Just (toBinder sv)
eFieldDeclBinder (FieldDeclBinding _bs _bv_)   = Nothing
eFieldDeclBinder (FieldDeclReference fv _fvWf) = Just (toIndex fv >>= toBinder)

eFieldDeclImplicitBinders :: Elab m => [FieldDecl w] -> [m Coq.Binder]
eFieldDeclImplicitBinders = mapMaybe eFieldDeclImplicitBinder

eFieldDeclImplicitBinder :: Elab m => FieldDecl w -> Maybe (m Coq.Binder)
eFieldDeclImplicitBinder (FieldDeclSort _bs sv _svWf)  = Just (toImplicitBinder sv)
eFieldDeclImplicitBinder (FieldDeclBinding _bs _bv_)   = Nothing
eFieldDeclImplicitBinder (FieldDeclReference fv _fvWf) = Just (toIndex fv >>= toImplicitBinder)

eFieldDeclIdentifiers :: Elab m => [FieldDecl w] -> [m Coq.Identifier]
eFieldDeclIdentifiers = mapMaybe eFieldDeclIdentifier

eFieldDeclIdentifier :: Elab m => FieldDecl w -> Maybe (m Coq.Identifier)
eFieldDeclIdentifier (FieldDeclSort _bs sv _svWf)  = Just (toId sv)
eFieldDeclIdentifier (FieldDeclBinding _bs _bv)    = Nothing
eFieldDeclIdentifier (FieldDeclReference fv _fvWf) = Just (toIndex fv >>= toId)

eFieldDeclFields :: Elab m => [FieldDecl w] -> m [Field w]
eFieldDeclFields = sequenceA . mapMaybe eFieldDeclField

eFieldDeclField :: Elab m => FieldDecl w -> Maybe (m (Field w))
eFieldDeclField (FieldDeclSort _bs sv _svWf)  = Just (pure (FieldSort (SVar sv)))
eFieldDeclField (FieldDeclBinding _bs _bv)    = Nothing
eFieldDeclField (FieldDeclReference fv _fvWf) = Just (FieldIndex . IVar <$> toIndex fv)

eFieldDeclRefs :: Elab m => [FieldDecl w] -> [m Coq.Term]
eFieldDeclRefs = mapMaybe eFieldDeclRef

eFieldDeclRef :: Elab m => FieldDecl w -> Maybe (m Coq.Term)
eFieldDeclRef (FieldDeclSort _bs sv _svWf)  = Just (toRef sv)
eFieldDeclRef (FieldDeclBinding _bs _bv)    = Nothing
eFieldDeclRef (FieldDeclReference fv _fvWf) = Just (toIndex fv >>= toRef)

eFieldDeclTypes :: Elab m => [FieldDecl w] -> [m Coq.Term]
eFieldDeclTypes = mapMaybe eFieldDeclType

eFieldDeclType :: Elab m => FieldDecl w -> Maybe (m Coq.Term)
eFieldDeclType (FieldDeclSort _bs sv _svWf)  = Just (toRef (typeNameOf sv))
eFieldDeclType (FieldDeclBinding _bs _bv)    = Nothing
eFieldDeclType (FieldDeclReference fv _fvWf) = Just (toIndex fv >>= toRef . typeNameOf)

fieldDeclToSymbolicField :: BindSpec -> FieldDecl w -> SymbolicField w
fieldDeclToSymbolicField scp fd = case fd of
  FieldDeclSort bs sv _svWf   -> SymFieldSort scp bs (SymSubtree scp sv)
  FieldDeclBinding _bs bv     -> SymFieldBinding scp bv
  FieldDeclReference fv _fvWf -> SymFieldReferenceFree scp fv

ctorDecl2Pattern :: Elab m => CtorDecl -> m Coq.Pattern
ctorDecl2Pattern (CtorVar cn rv _) = do
  iv <- toIndex rv
  Coq.PatCtor
    <$> toQualId cn
    <*> sequenceA [toId iv]
ctorDecl2Pattern (CtorReg cn fds) =
  Coq.PatCtor
    <$> toQualId cn
    <*> (sequenceA . catMaybes $
          [ case fd of
              FieldDeclSort _bs sv _svWf  -> Just (toId sv)
              FieldDeclBinding _bs _bv    -> Nothing
              FieldDeclReference fv _fvWf -> Just (toIndex fv >>= toId)
          | fd <- fds
          ])


evalRuleBindSpec :: ElabRuleM m => ETerm -> RuleBindSpec -> m ETerm
evalRuleBindSpec et Nil = pure et
evalRuleBindSpec et (rbs:.rbsi) = do
  et' <- evalRuleBindSpec et rbs
  case rbsi of
    RuleBsiBinding mv sts ->
      ECons et' (typeNameOf mv) . catMaybes <$>
        traverse symbolicFieldToField sts
    RuleBsiCall fn jv -> do
      ev <- lookupJudgementOutput fn jv
      pure (EAppend et' (EVar ev))
