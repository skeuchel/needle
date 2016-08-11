{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}

module KnotCore.DeBruijn.Core where

import KnotCore.Syntax

import Control.Applicative
import Data.Maybe
import Data.Traversable (traverse)

--  _  _
-- | \| |__ _ _ __  ___ ___
-- | .` / _` | '  \/ -_|_-<
-- |_|\_\__,_|_|_|_\___/__/

-- Representation of heterogeneous variable lists. This is a list
-- representing a list of variables from all namespaces in the
-- specifications. Unfortunately this is not modular for now.
data HVarlistVar =
  HVLV {
    hvarlistVarRoot       :: NameRoot,
    hvarlistVarSuffix     :: Suffix
  }
  deriving (Eq,Ord,Show)

-- Representation of a cutoff variable. Cutoffs always belong to a
-- single namespace.
data CutoffVar =
  CV {
    cutoffVarRoot      :: NameRoot,
    cutoffVarSuffix    :: Suffix,
    cutoffVarNamespace :: NamespaceTypeName
  }
  deriving (Eq,Ord,Show)

-- Representation of an index variable. Cutoffs always belong to a
-- single namespace.
data IndexVar =
  IndexVar {
    indexVarRoot       :: NameRoot,
    indexVarSuffix     :: Suffix,
    indexVarNamespace  :: NamespaceTypeName,
    indexVarSort       :: SortTypeName
  }
  deriving (Eq,Ord,Show)

toIndex :: EnvM m => FreeVariable -> m IndexVar
toIndex (FV nr suff ntn) = do
  Just stn <- lookupNamespaceSort ntn
  return $ IndexVar nr suff ntn stn

-- Representation of a trace of a namespace.
data TraceVar =
  TV {
    traceVarRoot       :: NameRoot,
    traceVarSuffix     :: Suffix,
    traceVarNamespace  :: NamespaceTypeName
  }
  deriving (Eq,Ord,Show)

-- Representation of an term variable.
data TermVar =
  TermVar {
    termVarRoot       :: NameRoot,
    termVarSuffix     :: Suffix,
    termVarSort       :: SortTypeName
  }
  deriving (Eq,Ord,Show)

--------------------------------------------------------------------------------
-- Symbolic Data
--------------------------------------------------------------------------------

data HVarlist
  = HV0
  | HVS NamespaceTypeName HVarlist
  | HVVar HVarlistVar
  | HVCall FunName STerm
  | HVAppend HVarlist HVarlist
  | HVDomainEnv ETerm
  deriving (Eq,Ord,Show)

data Cutoff
  = C0 NamespaceTypeName
  | CS Cutoff
  | CS' NamespaceTypeName Cutoff
  | CVar CutoffVar
  | CWeaken Cutoff HVarlist
  deriving (Eq,Ord,Show)

data Index
  = I0 NamespaceTypeName SortTypeName
  | IS Index
  | IVar IndexVar
  | IWeaken Index HVarlist
  | IShift Cutoff Index
  | IShift' Cutoff Index
  deriving (Eq,Ord,Show)

data Trace
  = T0 NamespaceTypeName
  | TS NamespaceTypeName Trace
  | TVar TraceVar
  | TWeaken Trace HVarlist
  deriving (Eq,Ord,Show)

data STerm
  = SVar SortVariable
  | SCtorVar SortTypeName CtorName Index
  | SCtorReg SortTypeName CtorName [Field 'WMV]
  | SShift Cutoff STerm
  | SShift' Cutoff STerm
  | SSubst Trace STerm STerm
  | SSubst' Trace STerm STerm
  | SSubstIndex Trace STerm Index
  | SWeaken STerm HVarlist
  deriving (Eq,Ord,Show)

data Field (w :: WithMV)
  = FieldSort STerm
  | FieldEnv ETerm
  | (w ~ 'WMV) =>
    FieldIndex Index

deriving instance Eq (Field w)
deriving instance Ord (Field w)
deriving instance Show (Field w)

fieldDeclToField :: EnvM m => FieldDecl w -> Maybe (m (Field w))
fieldDeclToField (FieldDeclSort _ sv _) = Just (pure (FieldSort (SVar sv)))

fieldDeclsToFields :: EnvM m => [FieldDecl w] -> m [Field w]
fieldDeclsToFields = sequenceA . mapMaybe fieldDeclToField

shiftField :: Cutoff -> Field w -> Field w
shiftField c (FieldSort st) = FieldSort (SShift' c st)

substField :: Trace -> STerm -> Field w -> Field w
substField x t (FieldSort st) = FieldSort (SSubst' x t st)

weakenField :: Field w -> HVarlist -> Field w
weakenField (FieldSort st) h = FieldSort (SWeaken st h)

data ETerm
  = EVar EnvVariable
  | ENil EnvTypeName
  | ECons ETerm NamespaceTypeName [Field 'WOMV]
  | EAppend ETerm ETerm
  | EShift Cutoff ETerm
  | EShift' Cutoff ETerm
  | ESubst Trace STerm ETerm
  | ESubst' Trace STerm ETerm
  | EWeaken ETerm HVarlist
  -- | ECall FunName JudgementVariable EnvTypeName
  deriving (Eq,Ord,Show)

data Lookup
  = Lookup ETerm Index [Field 'WOMV]
  deriving (Eq,Ord,Show)

data InsertEnv
  = InsertEnv Cutoff ETerm ETerm
  deriving (Eq,Ord,Show)

data InsertEnvHyp
  = InsertEnvHyp Hypothesis InsertEnv
  deriving (Eq,Ord,Show)

data InsertEnvTerm
  = InsertEnvVar InsertEnvHyp
  | InsertEnvCons NamespaceTypeName [Field 'WOMV] InsertEnvTerm
  | InsertEnvWeaken InsertEnvTerm ETerm
  deriving (Eq,Ord,Show)

data SubstEnv
  = SubstEnv ETerm [Field 'WOMV] STerm Trace ETerm ETerm
  deriving (Eq,Ord,Show)

data SubstEnvHyp
  = SubstEnvHyp Hypothesis SubstEnv
  deriving (Eq,Ord,Show)

data SubstEnvTerm
  = SubstEnvVar SubstEnvHyp
  | SubstEnvCons NamespaceTypeName [Field 'WOMV] SubstEnvTerm
  | SubstEnvWeaken SubstEnvTerm ETerm
  deriving (Eq,Ord,Show)

data JudgementEnv
  = JudgementEnvTerm        ETerm
  | JudgementEnvUnderscore
  | JudgementEnvNothing
  deriving (Eq,Ord,Show)

data Prop
  = PEqTerm STerm STerm
  | forall w. PEqField (Field w) (Field w)
  | PAnd [Prop]
  | PJudgement RelationTypeName JudgementEnv [Field 'WOMV] [ETerm]
  | PEqHvl HVarlist HVarlist

data WellFormedIndex
  = WfIndex HVarlist Index
  deriving (Eq,Ord,Show)

data WellFormedSort
  = WfSort HVarlist STerm
  deriving (Eq,Ord,Show)

data WellFormedSortHyp
  = WellFormedSortHyp
    { wfsHyp             ::   Hypothesis
    , wfsType            ::   WellFormedSort
    }
  deriving (Eq,Ord,Show)

data WellFormedIndexHyp
  = WellFormedIndexHyp
    { wfiHyp            ::   Hypothesis
    , wfiType           ::   WellFormedIndex
    }
  deriving (Eq,Ord,Show)

data WellFormedHyp
  = WellFormedHypSort WellFormedSortHyp
  | WellFormedHypIndex WellFormedIndexHyp
  deriving (Eq,Ord,Show)

data WellFormedSortTerm
  = WellFormedSortVar WellFormedSortHyp
  | WellFormedSortShift InsertHvlTerm WellFormedSortTerm
  | WellFormedSortSubst WellFormedSortTerm SubstHvlTerm WellFormedSortTerm
  | WellFormedSortJudgement Int SortTypeName JudgementVariable RelationTypeName ETerm [Field 'WOMV] [ETerm]
  deriving (Eq,Ord,Show)

data WellFormedIndexTerm
  = WellFormedIndexVar WellFormedIndexHyp
  | WellFormedIndexShift InsertHvlTerm WellFormedIndexTerm
  | WellFormedIndexSubst WellFormedSortTerm SubstHvlTerm WellFormedIndexTerm
  deriving (Eq,Ord,Show)

data InsertHvlTerm
  = InsertHvlEnv
    { insertHvlEnv      ::   InsertEnvTerm
    }
  | InsertHvlWeaken
    { insertHvlRec      ::   InsertHvlTerm
    , insertHvlWeaken   ::   HVarlist
    }
  deriving (Eq,Ord,Show)

data SubstHvlTerm
  = SubstHvlEnv
    { substHvlEnv      ::   SubstEnvTerm
    }
  | SubstHvlWeaken
    { substHvlRec      ::   SubstHvlTerm
    , substHvlWeaken   ::   HVarlist
    }
  deriving (Eq,Ord,Show)

data WellFormedFormula
  = WfFormHyp  WellFormedHyp
  | WfShift    WellFormedFormula
  deriving (Eq,Ord,Show)

data HVarlistInsertion
  = HVarlistInsertion Cutoff HVarlist HVarlist
  deriving (Eq,Ord,Show)

data SubstHvl
  = SubstHvl HVarlist Trace HVarlist HVarlist
  deriving (Eq,Ord,Show)

data SubHvl
  = SubHvl [NamespaceTypeName] HVarlist
  deriving (Eq,Ord,Show)

--------------------------------------------------------------------------------
-- Typenames
--------------------------------------------------------------------------------

instance TypeNameOf CutoffVar NamespaceTypeName where
  typeNameOf = cutoffVarNamespace
instance TypeNameOf IndexVar NamespaceTypeName where
  typeNameOf = indexVarNamespace
instance TypeNameOf TermVar SortTypeName where
  typeNameOf = termVarSort
instance TypeNameOf TraceVar NamespaceTypeName where
  typeNameOf = traceVarNamespace

class SortOf a where
  sortOf :: a -> SortTypeName

-- instance TypeNameOf a SortTypeName => SortOf a where
--   sortOf = typeNameOf
instance SortOf SortVariable where
  sortOf (SV _ _ stn) = stn
instance SortOf IndexVar where
  sortOf (IndexVar _ _ _ stn) = stn

instance TypeNameOf Cutoff NamespaceTypeName where
  typeNameOf (C0 ntn)      = ntn
  typeNameOf (CS c)        = typeNameOf c
  typeNameOf (CS' _ c)     = typeNameOf c
  typeNameOf (CVar cv)     = typeNameOf cv
  typeNameOf (CWeaken c _) = typeNameOf c

instance TypeNameOf Trace NamespaceTypeName where
  typeNameOf (T0 ntn)      = ntn
  typeNameOf (TS _ x)      = typeNameOf x
  typeNameOf (TVar xv)     = typeNameOf xv
  typeNameOf (TWeaken x _) = typeNameOf x

instance TypeNameOf Index NamespaceTypeName where
  typeNameOf (I0 ntn _)    = ntn
  typeNameOf (IS i)        = typeNameOf i
  typeNameOf (IVar iv)     = typeNameOf iv
  typeNameOf (IWeaken i _) = typeNameOf i
  typeNameOf (IShift _ i)  = typeNameOf i
  typeNameOf (IShift' _ i) = typeNameOf i

instance TypeNameOf WellFormedIndex NamespaceTypeName where
  typeNameOf (WfIndex _ i) = typeNameOf i

instance TypeNameOf WellFormedSort SortTypeName where
  typeNameOf (WfSort _ s)  = typeNameOf s

instance SortOf Index where
  sortOf (I0 _ stn)    = stn
  sortOf (IS i)        = sortOf i
  sortOf (IVar iv)     = sortOf iv
  sortOf (IWeaken i _) = sortOf i
  sortOf (IShift _ i)  = sortOf i
  sortOf (IShift' _ i) = sortOf i

instance SortOf STerm where
  sortOf (SVar sv)           = sortOf sv
  sortOf (SCtorVar stn _ _)  = stn
  sortOf (SCtorReg stn _ _)  = stn
  sortOf (SShift _ t)        = sortOf t
  sortOf (SShift' _ t)       = sortOf t
  sortOf (SSubst _ _ t)      = sortOf t
  sortOf (SSubst' _ _ t)     = sortOf t
  sortOf (SSubstIndex _ _ i) = sortOf i
  sortOf (SWeaken t _)       = sortOf t

instance TypeNameOf STerm SortTypeName where
  typeNameOf = sortOf

instance TypeNameOf ETerm EnvTypeName where
  typeNameOf (EVar ev)        = typeNameOf ev
  typeNameOf (ENil etn)       = etn
  typeNameOf (ECons et _ _)   = typeNameOf et
  typeNameOf (EAppend et _)   = typeNameOf et
  typeNameOf (EShift _ et)    = typeNameOf et
  typeNameOf (EShift' _ et)   = typeNameOf et
  typeNameOf (ESubst _ _ et)  = typeNameOf et
  typeNameOf (ESubst' _ _ et) = typeNameOf et
  typeNameOf (EWeaken et _)   = typeNameOf et

instance TypeNameOf InsertEnvHyp (NamespaceTypeName, EnvTypeName) where
  typeNameOf (InsertEnvHyp _ (InsertEnv cv ev _)) = (typeNameOf cv, typeNameOf ev)
instance TypeNameOf InsertEnvTerm (NamespaceTypeName, EnvTypeName) where
  typeNameOf (InsertEnvVar hyp)       = typeNameOf hyp
  typeNameOf (InsertEnvCons _ _ iet)  = typeNameOf iet
  typeNameOf (InsertEnvWeaken iet _)  = typeNameOf iet

instance TypeNameOf SubstEnvHyp (NamespaceTypeName, EnvTypeName) where
  typeNameOf (SubstEnvHyp _ (SubstEnv et0 _ _ x _ _)) = (typeNameOf x, typeNameOf et0)
instance TypeNameOf SubstEnvTerm (NamespaceTypeName, EnvTypeName) where
  typeNameOf (SubstEnvVar hyp)       = typeNameOf hyp
  typeNameOf (SubstEnvCons _ _ set)  = typeNameOf set
  typeNameOf (SubstEnvWeaken set _)  = typeNameOf set

instance TypeNameOf InsertHvlTerm NamespaceTypeName where
  typeNameOf (InsertHvlEnv ins)     = fst (typeNameOf ins)
  typeNameOf (InsertHvlWeaken rec _) = typeNameOf rec

instance TypeNameOf SubstHvlTerm NamespaceTypeName where
  typeNameOf (SubstHvlEnv sub)     = fst (typeNameOf sub)
  typeNameOf (SubstHvlWeaken rec _) = typeNameOf rec

instance TypeNameOf WellFormedIndexHyp NamespaceTypeName where
  typeNameOf (WellFormedIndexHyp _ wfi) = typeNameOf wfi

instance TypeNameOf WellFormedIndexTerm NamespaceTypeName where
  typeNameOf (WellFormedIndexVar hyp)     = typeNameOf hyp
  typeNameOf (WellFormedIndexShift _ wfi) = typeNameOf wfi
  typeNameOf (WellFormedIndexSubst _ _ wfi) = typeNameOf wfi

instance TypeNameOf WellFormedSortHyp SortTypeName where
  typeNameOf (WellFormedSortHyp _ wfi) = typeNameOf wfi

instance TypeNameOf WellFormedSortTerm SortTypeName where
  typeNameOf (WellFormedSortVar hyp)       = typeNameOf hyp
  typeNameOf (WellFormedSortShift _ wfi)   = typeNameOf wfi
  typeNameOf (WellFormedSortSubst _ _ wfi) = typeNameOf wfi
  typeNameOf (WellFormedSortJudgement _ stn _ _ _ _ _) = stn

instance SortOf WellFormedIndex where
  sortOf (WfIndex _ i) = sortOf i

instance SortOf WellFormedSort where
  sortOf (WfSort _ s)  = sortOf s

symbolicTermToSTerm :: EnvM m => SymbolicTerm -> m STerm
symbolicTermToSTerm (SymSubtree _ sv)     =
  pure (SVar sv)
symbolicTermToSTerm (SymCtorVarFree _ cn mv)  = do
  stn <- lookupCtorType cn
  SCtorVar stn cn . IVar <$> toIndex mv
symbolicTermToSTerm (SymCtorVarBound _ cn mv _ diff) = do
  stn <- lookupCtorType cn
  let ntn = typeNameOf mv
  pure (SCtorVar stn cn (IWeaken (I0 ntn stn) (evalBindSpec HV0 diff)))
symbolicTermToSTerm (SymCtorReg _ cn sfs) = do
  stn <- lookupCtorType cn
  SCtorReg stn cn . catMaybes <$> traverse symbolicFieldToField sfs
symbolicTermToSTerm (SymWeaken _ _ st diff)   =
  SWeaken
    <$> symbolicTermToSTerm st
    <*> pure (evalBindSpec HV0 diff)
symbolicTermToSTerm (SymSubst _ mv st1 st2)    =
  SSubst
    <$> pure (T0 (typeNameOf mv))
    <*> symbolicTermToSTerm st1
    <*> symbolicTermToSTerm st2

symbolicFieldToField :: EnvM m => SymbolicField w -> m (Maybe (Field w))
symbolicFieldToField (SymFieldSort _ _ st)      = Just . FieldSort <$> symbolicTermToSTerm st
symbolicFieldToField (SymFieldEnv{})            = error "NOT IMPLEMENTED"
symbolicFieldToField (SymFieldBinding{})        = pure Nothing
symbolicFieldToField (SymFieldReferenceFree{})  = error "NOT IMPLEMENTED"
symbolicFieldToField (SymFieldReferenceBound{}) = error "NOT IMPLEMENTED"

symbolicEnvToETerm :: EnvM m => SymbolicEnv -> m ETerm
symbolicEnvToETerm _se = case _se of
  SymEnvVar ev          -> pure (EVar ev)
  SymEnvNil etn         -> pure (ENil etn)
  SymEnvCons ntn se sts ->
    ECons
      <$> symbolicEnvToETerm se
      <*> pure ntn
      <*> (catMaybes <$> traverse symbolicFieldToField sts)
  SymEnvAppend l r ->
    EAppend
      <$> symbolicEnvToETerm l
      <*> symbolicEnvToETerm r
  -- SymEnvCall fn jv ->
  --   ECall fn jv <$> lookupRelationOutput fn (typeNameOf jv)

--  ___          _           _   _
-- | __|_ ____ _| |_  _ __ _| |_(_)___ _ _
-- | _|\ V / _` | | || / _` |  _| / _ \ ' \
-- |___|\_/\__,_|_|\_,_\__,_|\__|_\___/_||_|

evalBindSpecItem :: BindSpecItem -> HVarlist
evalBindSpecItem (BsiBinding mv)  = HVS (typeNameOf mv) HV0
evalBindSpecItem (BsiCall  fn sn) = HVCall fn (SVar sn)

evalBindSpec :: HVarlist -> BindSpec -> HVarlist
evalBindSpec h Nil = h
evalBindSpec h (bs :. bsi) = HVAppend (evalBindSpec h bs) (evalBindSpecItem bsi)
