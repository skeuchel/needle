{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

module KnotCore.Elaboration.Identifiers where


import           KnotCore.Syntax
import           KnotCore.Environment
import           KnotCore.Elaboration.Monad

import qualified Coq.Syntax as Coq

import           Data.List ((\\),intercalate)
import qualified Data.Map as M
import           Data.Traversable (for)

--  ___    _         _   _  __ _
-- |_ _|__| |___ _ _| |_(_)/ _(_)___ _ _ ___
--  | |/ _` / -_) ' \  _| |  _| / -_) '_(_-<
-- |___\__,_\___|_||_\__|_|_| |_\___|_| /__/

class Ident a where
  toId     :: Elab m => a -> m Coq.Identifier
  toQualId :: Elab m => a -> m Coq.QualId
  toQualId = fmap Coq.Ident . toId
  toName   :: Elab m => a -> m Coq.Name
  toName = fmap Coq.NameIdent . toId
  toRef    :: Elab m => a -> m Coq.Term
  toRef = fmap Coq.TermQualId . toQualId

instance Ident SortTypeName where
  toId (STN _loc s) = return $ Coq.ID s
instance Ident NamespaceTypeName where
  toId (NTN _loc s) = return $ Coq.ID s
instance Ident RelationTypeName where
  toId (RTN _loc s) = return $ Coq.ID s
instance Ident EnvTypeName where
  toId (ETN _loc s) = return $ Coq.ID s
instance Ident FunName where
  toId = return . Coq.ID . fnId
instance Ident CtorName where
  toId = return . Coq.ID . cnId
instance Ident Coq.Identifier where
  toId = return

{-------------------------------------------------------------------------------
   _  _
  | \| |__ _ _ __  ___ ____ __  __ _ __ ___
  | .` / _` | '  \/ -_|_-< '_ \/ _` / _/ -_)
  |_|\_\__,_|_|_|_\___/__/ .__/\__,_\__\___|
                         |_|
-------------------------------------------------------------------------------}

-- This is the type representing all the namespaces that are part of
-- this specification. It contains one data constructor per declared
-- namespace.
idTypeNamespace :: Elab m => m Coq.Identifier
idTypeNamespace = return $ Coq.ID "Namespace"

idCtorNamespace :: Elab m => NamespaceTypeName -> m Coq.Identifier
idCtorNamespace (NTN _loc ntn) = return $ Coq.ID ntn

idLemmaEqNamespaceDec :: Elab m => m Coq.Identifier
idLemmaEqNamespaceDec = return $ Coq.ID "eq_namespace_dec"

{-------------------------------------------------------------------------------
   _  ___   __        _ _    _
  | || \ \ / /_ _ _ _| (_)__| |_
  | __ |\ V / _` | '_| | (_-<  _|
  |_||_| \_/\__,_|_| |_|_/__/\__|

-------------------------------------------------------------------------------}

idTypeHVarlist :: Elab m => m Coq.Identifier
idTypeHVarlist = return $ Coq.ID "Hvl"

idCtorHVarlistNil :: Elab m => m Coq.Identifier
idCtorHVarlistNil = return $ Coq.ID "H0"

idCtorHVarlistCons :: Elab m => m Coq.Identifier
idCtorHVarlistCons = return $ Coq.ID "HS"

idAppendHVarlist :: Elab m => m Coq.Identifier
idAppendHVarlist = return $ Coq.ID "appendHvl"

idTacticSpecializeHVarlistNil :: Elab m => m Coq.Identifier
idTacticSpecializeHVarlistNil = do
  Coq.ID nil <- idCtorHVarlistNil
  return . Coq.ID $ "specialize_" ++ nil

idLemmaHVarlistAppendAssoc :: Elab m => m Coq.Identifier
idLemmaHVarlistAppendAssoc = return $ Coq.ID "appendHvl_assoc"


idRelationHVarlistInsert :: Elab m => NamespaceTypeName -> m Coq.Identifier
idRelationHVarlistInsert (NTN _loc ntn) =
  return (Coq.ID $ "shifthvl_" ++ ntn)

idRelationHVarlistInsertHere :: Elab m => NamespaceTypeName -> m Coq.Identifier
idRelationHVarlistInsertHere (NTN _loc ntn) =
  return (Coq.ID $ "shifthvl_" ++ ntn ++ "_here")

idRelationHVarlistInsertThere :: Elab m => NamespaceTypeName -> NamespaceTypeName -> m Coq.Identifier
idRelationHVarlistInsertThere (NTN _loc ntn) (NTN _loc' ntn') =
  return (Coq.ID $ "shifthvl_" ++ ntn ++ "_there_" ++ ntn')

idLemmaWeakenRelationHVarlistInsert :: Elab m => NamespaceTypeName -> m Coq.Identifier
idLemmaWeakenRelationHVarlistInsert (NTN _loc ntn) =
  return (Coq.ID $ "weaken_shifthvl_" ++ ntn)


idTypeSubstHvl :: Elab m => NamespaceTypeName -> m Coq.Identifier
idTypeSubstHvl (NTN _loc ntn) =
  return (Coq.ID $ "substhvl_" ++ ntn)

idCtorSubstHvlHere :: Elab m => NamespaceTypeName -> m Coq.Identifier
idCtorSubstHvlHere (NTN _loc ntn) =
  return (Coq.ID $ "substhvl_" ++ ntn ++ "_here")

idCtorSubstHvlThere :: Elab m => NamespaceTypeName -> NamespaceTypeName -> m Coq.Identifier
idCtorSubstHvlThere (NTN _loc ntn) (NTN _loc' ntn') =
  return (Coq.ID $ "substhvl_" ++ ntn ++ "_there_" ++ ntn')

idLemmaWeakenSubstHvl :: Elab m => NamespaceTypeName -> m Coq.Identifier
idLemmaWeakenSubstHvl (NTN _loc ntn) =
  return (Coq.ID $ "weaken_substhvl_" ++ ntn)

idLemmaSubstHvlWfIndex :: Elab m => NamespaceTypeName -> NamespaceTypeName -> m Coq.Identifier
idLemmaSubstHvlWfIndex ntn1 ntn2 = do
  Coq.ID substhvl <- idTypeSubstHvl ntn1
  Coq.ID wfindex  <- idFunctionWellFormedIndex

  return (Coq.ID $ substhvl ++ "_" ++ wfindex ++ "_" ++ ntnId ntn2)

setLemmaSubstHvlWfIndex :: Elab m => m [Coq.Identifier]
setLemmaSubstHvlWfIndex = do
  ntns <- getNamespaces
  sequenceA [ idLemmaSubstHvlWfIndex ntn1 ntn2 | ntn1 <- ntns, ntn2 <- ntns ]

{-------------------------------------------------------------------------------
  __      __        _
  \ \    / /__ __ _| |_____ _ _
   \ \/\/ / -_) _` | / / -_) ' \
    \_/\_/\___\__,_|_\_\___|_||_|

-------------------------------------------------------------------------------}

idClassWeaken :: Elab m => m Coq.Identifier
idClassWeaken = return $ Coq.ID "Weaken"

idMethodWeaken :: Elab m => m Coq.Identifier
idMethodWeaken = return $ Coq.ID "weaken"

idMethodWeakenInj :: Elab m => m Coq.Identifier
idMethodWeakenInj = return $ Coq.ID "weaken_inj"

idMethodWeakenAppend :: Elab m => m Coq.Identifier
idMethodWeakenAppend = return $ Coq.ID "weaken_append"

{-------------------------------------------------------------------------------
   ___         _
  |_ _|_ _  __| |_____ __
   | || ' \/ _` / -_) \ /
  |___|_||_\__,_\___/_\_\

    Index is a datatype representing de Bruijn indices (natural numbers):

      Inductive Index (a : Namespace) : Type :=
        | I0
        | IS : Index a -> Index a.

    A single datatype is used to prevent duplicating this type and client code
    for each namespace. Nevertheless, the Index type has the namespace as a
    phantom type to allow for namespace specific type-class intances.

-------------------------------------------------------------------------------}

idFamilyIndex :: Elab m => m Coq.Identifier
idFamilyIndex = return $ Coq.ID "Index"

idFamilyIndexZero :: Elab m => m Coq.Identifier
idFamilyIndexZero = return $ Coq.ID "I0"

idFamilyIndexSucc :: Elab m => m Coq.Identifier
idFamilyIndexSucc = return $ Coq.ID "IS"

typeIndex :: Elab m => NamespaceTypeName -> m Coq.Term
typeIndex ntn =
  Coq.TermApp
    <$> (idFamilyIndex >>= toRef)
    <*> sequenceA [idCtorNamespace ntn >>= toRef]

idLemmaEqIndexDec :: Elab m => m Coq.Identifier
idLemmaEqIndexDec = return $ Coq.ID "eq_index_dec"

idFunctionWeakenIndex :: Elab m => NamespaceTypeName -> m Coq.Identifier
idFunctionWeakenIndex ntn =
  return . Coq.ID $ "weakenIndex" ++ ntnId ntn

idLemmaWeakenIndexAppend :: Elab m => NamespaceTypeName -> m Coq.Identifier
idLemmaWeakenIndexAppend ntn =
  return $ Coq.ID $ "weakenIndex" ++ ntnId ntn ++ "_append"

idInstanceWeakenIndex :: Elab m => NamespaceTypeName -> m Coq.Identifier
idInstanceWeakenIndex ntn =
  return . Coq.ID $ "WeakenIndex" ++ ntnId ntn

idFunctionWellFormedIndex :: Elab m => m Coq.Identifier
idFunctionWellFormedIndex =
  return $ Coq.ID "wfindex"

{-------------------------------------------------------------------------------
    ___     _        __  __
   / __|  _| |_ ___ / _|/ _|
  | (_| || |  _/ _ \  _|  _|
   \___\_,_|\__\___/_| |_|

    Cutoff is a datatype representing cutoffs for the shift operations:

      Inductive Cutoff (a : Namespace) : Type :=
        | I0
        | IS : Cutoff a -> Cutoff a.

    The cutoff is representing the context depth after variable insertion. More
    concretely, after inserting a new variable x of namespace α

         Γ,Δ   ⟶   Γ,x,Δ

    we need to update all indices pointing into Γ, i.e. variables that
    appear before x in the context. This is implemented by
    the shift-operation. The cutoff parameter represents the relevant part of Δ,
    i.e. the part that concerns itself with the namespace α: it is the number
    of α-variable bindings in Δ.

    As for indices, we use a single datatype with a phantom parameter.

-------------------------------------------------------------------------------}

idFamilyCutoff :: Elab m => m Coq.Identifier
idFamilyCutoff = return $ Coq.ID "Cutoff"

idFamilyCutoffZero :: Elab m => m Coq.Identifier
idFamilyCutoffZero = return $ Coq.ID "C0"

idFamilyCutoffSucc :: Elab m => m Coq.Identifier
idFamilyCutoffSucc = return $ Coq.ID "CS"

typeCutoff :: Elab m => NamespaceTypeName -> m Coq.Term
typeCutoff ntn =
  Coq.TermApp
    <$> (idFamilyCutoff >>= toRef)
    <*> sequenceA [idCtorNamespace ntn >>= toRef]

idFunctionWeakenCutoff :: Elab m => NamespaceTypeName -> m Coq.Identifier
idFunctionWeakenCutoff ntn =
  return . Coq.ID $ "weakenCutoff" ++ ntnId ntn

idLemmaWeakenCutoffAppend :: Elab m => NamespaceTypeName -> m Coq.Identifier
idLemmaWeakenCutoffAppend ntn =
  return $ Coq.ID $ "weakenCutoff" ++ ntnId ntn ++ "_append"

idInstanceWeakenCutoff :: Elab m => NamespaceTypeName -> m Coq.Identifier
idInstanceWeakenCutoff ntn =
  return . Coq.ID $ "WeakenCutoff" ++ ntnId ntn

setLemmaWeakenCutoffAppend :: Elab m => m [Coq.Identifier]
setLemmaWeakenCutoffAppend =
  getNamespaces >>= traverse idLemmaWeakenCutoffAppend

{-------------------------------------------------------------------------------
   _____
  |_   _| _ __ _ __ ___
    | || '_/ _` / _/ -_)
    |_||_| \__,_\__\___|

-------------------------------------------------------------------------------}

idFamilyTrace :: Elab m => m Coq.Identifier
idFamilyTrace = return $ Coq.ID "Trace"

idFamilyTraceNil :: Elab m => m Coq.Identifier
idFamilyTraceNil = return $ Coq.ID "X0"

idFamilyTraceCons :: Elab m => m Coq.Identifier
idFamilyTraceCons = return $ Coq.ID "XS"

typeTrace :: Elab m => NamespaceTypeName -> m Coq.Term
typeTrace ntn =
  Coq.TermApp
    <$> (idFamilyTrace >>= toRef)
    <*> sequenceA [idCtorNamespace ntn >>= toRef]

idFunctionWeakenTrace :: Elab m => m Coq.Identifier
idFunctionWeakenTrace =
  return $ Coq.ID "weakenTrace"

idLemmaWeakenTraceAppend :: Elab m => m Coq.Identifier
idLemmaWeakenTraceAppend =
  return $ Coq.ID "weakenTrace_append"

idInstanceWeakenTrace :: Elab m => m Coq.Identifier
idInstanceWeakenTrace =
  return $ Coq.ID "WeakenTrace"

setLemmaWeakenTraceAppend :: Elab m => m [Coq.Identifier]
setLemmaWeakenTraceAppend =
  sequenceA [idLemmaWeakenTraceAppend]

{-------------------------------------------------------------------------------
   ___ _    _  __ _
  / __| |_ (_)/ _| |_
  \__ \ ' \| |  _|  _|
  |___/_||_|_|_|  \__|

-------------------------------------------------------------------------------}

idFunctionShiftIndex :: Elab m => NamespaceTypeName -> m Coq.Identifier
idFunctionShiftIndex ntn =
  do
    sr <- getShiftRoot ntn
    return (Coq.ID $ sr ++ "Index")

idFunctionShift :: Elab m => NamespaceTypeName -> SortTypeName -> m Coq.Identifier
idFunctionShift ntn (STN _loc stn) =
  do
    sr <- getShiftRoot ntn
    return (Coq.ID $ sr ++ stn)

setFunctionShift :: Elab m => m [Coq.Identifier]
setFunctionShift = do
  deps <- meSortNamespaceDeps <$> getMetaEnvironments
  sequenceA
    [ idFunctionShift ntn stn
    | (stn,ntns) <- M.toList deps, ntn <- ntns
    ]

idFunctionWeakenTerm :: Elab m => SortTypeName -> m Coq.Identifier
idFunctionWeakenTerm stn =
  return . Coq.ID $ "weaken" ++ stnId stn

idLemmaWeakenTermAppend :: Elab m => SortTypeName -> m Coq.Identifier
idLemmaWeakenTermAppend stn =
  return $ Coq.ID $ "weaken" ++ stnId stn ++ "_append"

idInstanceWeakenTerm :: Elab m => SortTypeName -> m Coq.Identifier
idInstanceWeakenTerm stn =
  return . Coq.ID $ "Weaken" ++ stnId stn

{-------------------------------------------------------------------------------
   ___      _       _
  / __|_  _| |__ __| |_
  \__ \ || | '_ (_-<  _|
  |___/\_,_|_.__/__/\__|

-------------------------------------------------------------------------------}

idFunctionSubstIndex :: Elab m => NamespaceTypeName -> m Coq.Identifier
idFunctionSubstIndex ntn =
  do
    sr <- getSubstRoot ntn
    return (Coq.ID $ sr ++ "Index")

idFunctionSubst :: Elab m => NamespaceTypeName -> SortTypeName -> m Coq.Identifier
idFunctionSubst ntn (STN _loc stn) =
  do
    sr <- getSubstRoot ntn
    return (Coq.ID $ sr ++ stn)

{-------------------------------------------------------------------------------
   ___         _         _   _            ___     _
  |_ _|_ _  __| |_  _ __| |_(_)___ _ _   / __| __| |_  ___ _ __  ___ ___
   | || ' \/ _` | || / _|  _| / _ \ ' \  \__ \/ _| ' \/ -_) '  \/ -_|_-<
  |___|_||_\__,_|\_,_\__|\__|_\___/_||_| |___/\__|_||_\___|_|_|_\___/__/

-------------------------------------------------------------------------------}

-- Induction principle
inductionName :: Elab m => String -> m String
inductionName s =
  return ("ind_" ++ s)

idInductionSort :: Elab m => SortTypeName -> m Coq.Identifier
idInductionSort stn = Coq.ID <$> inductionName (stnId stn)

idInductionSortGroup :: Elab m => SortGroupTypeName -> m Coq.Identifier
idInductionSortGroup sgtn = Coq.ID <$> inductionName (sgtnId sgtn)

inductionNameWellFormed :: Elab m => String -> m String
inductionNameWellFormed s =
  return ("ind_wf" ++ s)

idInductionWellFormedSort :: Elab m => SortTypeName -> m Coq.Identifier
idInductionWellFormedSort stn = Coq.ID <$> inductionNameWellFormed (stnId stn)

idInductionWellFormedSortGroup :: Elab m => SortGroupTypeName -> m Coq.Identifier
idInductionWellFormedSortGroup sgtn = Coq.ID <$> inductionNameWellFormed (sgtnId sgtn)

idFunctionInductionSort :: Elab m => FunGroupName -> SortTypeName -> m Coq.Identifier
idFunctionInductionSort (FGN fgn) (STN _loc stn) =
  return (Coq.ID $ "ind_" ++ fgn ++ "_" ++ stn)

idFunctionInductionSortGroup :: Elab m => FunGroupName -> SortGroupTypeName -> m Coq.Identifier
idFunctionInductionSortGroup (FGN fgn) (SGTN sgtn) =
  return (Coq.ID $ "ind_" ++ fgn ++ "_" ++ sgtn)

idInductionRelation :: Elab m => RelationTypeName -> m Coq.Identifier
idInductionRelation (RTN _loc rtn) = return (Coq.ID $ rtn ++ "_ind")

{-------------------------------------------------------------------------------
   _             _
  | |   ___  ___| |___  _ _ __
  | |__/ _ \/ _ \ / / || | '_ \
  |____\___/\___/_\_\\_,_| .__/
                         |_|
-------------------------------------------------------------------------------}

idTypeLookup :: Elab m => CtorName -> m Coq.Identifier
idTypeLookup cn =
  return (Coq.ID $ "lookup_" ++ cnId cn)

setTypeLookup :: Elab m => m [Coq.Identifier]
setTypeLookup = do
  envCtors <- M.toList . meNamespaceEnvCtor <$> getMetaEnvironments
  sequenceA [ idTypeLookup cn | (_, (_, cn)) <- envCtors ]

idCtorLookupHere :: Elab m => CtorName -> m Coq.Identifier
idCtorLookupHere cn = do
  Coq.ID lookup <- idTypeLookup cn
  return (Coq.ID $ lookup ++ "_here")

idCtorLookupThere :: Elab m => CtorName -> CtorName -> m Coq.Identifier
idCtorLookupThere cn cn' = do
  Coq.ID lookup <- idTypeLookup cn
  return (Coq.ID $ lookup ++ "_there_" ++ cnId cn')

idLemmaLookupFunctional :: Elab m => CtorName -> m Coq.Identifier
idLemmaLookupFunctional cn = do
  Coq.ID lk <- idTypeLookup cn
  return (Coq.ID $ lk ++ "_functional")

idLookupInversionHere :: Elab m => CtorName -> m Coq.Identifier
idLookupInversionHere cn = do
  Coq.ID lk <- idTypeLookup cn
  return (Coq.ID $ lk ++ "_inversion_here")

idLemmaLookupWellformedIndex :: Elab m => CtorName -> m Coq.Identifier
idLemmaLookupWellformedIndex cn = do
  Coq.ID lk <- idTypeLookup cn
  return (Coq.ID $ lk ++ "_wfindex")

setLemmaLookupWellformedIndex :: Elab m => m [Coq.Identifier]
setLemmaLookupWellformedIndex = do
  envCtors <- M.toList . meNamespaceEnvCtor <$> getMetaEnvironments
  sequenceA [ idLemmaLookupWellformedIndex cn | (_, (_, cn)) <- envCtors ]

{-------------------------------------------------------------------------------
   ___                  _     ___
  |_ _|_ _  ___ ___ _ _| |_  | __|_ ___ __
   | || ' \(_-</ -_) '_|  _| | _|| ' \ V /
  |___|_||_/__/\___|_|  \__| |___|_||_\_/

-------------------------------------------------------------------------------}

idTypeInsertEnv :: Elab m => CtorName -> m Coq.Identifier
idTypeInsertEnv cn =
  return (Coq.ID $ "shift_" ++ cnId cn)

setTypeInsertEnv :: Elab m => m [Coq.Identifier]
setTypeInsertEnv = getEnvCtors >>= traverse idTypeInsertEnv

idCtorInsertEnvHere :: Elab m => CtorName -> m Coq.Identifier
idCtorInsertEnvHere cn =
  return (Coq.ID $ "shift_" ++ cnId cn ++ "_here")

idCtorInsertEnvThere :: Elab m => CtorName -> CtorName -> m Coq.Identifier
idCtorInsertEnvThere cn cn' =
  return (Coq.ID $ "shift" ++ cnId cn ++ "_there_" ++ cnId cn')

idLemmaWeakenInsertEnv :: Elab m => CtorName -> m Coq.Identifier
idLemmaWeakenInsertEnv cn =
  return (Coq.ID $ "weaken_shift_" ++ cnId cn)

setLemmaWeakenInsertEnv :: Elab m => m [Coq.Identifier]
setLemmaWeakenInsertEnv = getEnvCtors >>= traverse idLemmaWeakenInsertEnv

idLemmaInsertEnvInsertHvl :: Elab m => EnvTypeName -> NamespaceTypeName -> m Coq.Identifier
idLemmaInsertEnvInsertHvl etn ntn = do
  cn <- getEnvCtorName etn ntn
  Coq.ID insertEnv <- idTypeInsertEnv cn
  Coq.ID insertHvl <- idRelationHVarlistInsert ntn

  return (Coq.ID $ insertEnv ++ "_" ++ insertHvl)

{-------------------------------------------------------------------------------
   ___      _       _     ___
  / __|_  _| |__ __| |_  | __|_ ___ __
  \__ \ || | '_ (_-<  _| | _|| ' \ V /
  |___/\_,_|_.__/__/\__| |___|_||_\_/

-------------------------------------------------------------------------------}

idTypeSubstEnv :: Elab m => CtorName -> m Coq.Identifier
idTypeSubstEnv cn =
  return (Coq.ID $ "subst_" ++ cnId cn)

setTypeSubstEnv :: Elab m => m [Coq.Identifier]
setTypeSubstEnv = getEnvCtors >>= traverse idTypeSubstEnv

idCtorSubstEnvHere :: Elab m => CtorName -> m Coq.Identifier
idCtorSubstEnvHere cn =
  return (Coq.ID $ "subst_" ++ cnId cn ++ "_here")

idCtorSubstEnvThere :: Elab m => CtorName -> CtorName -> m Coq.Identifier
idCtorSubstEnvThere cn cn' =
  return (Coq.ID $ "subst_" ++ cnId cn ++ "_there_" ++ cnId cn')

idLemmaWeakenSubstEnv :: Elab m => CtorName -> m Coq.Identifier
idLemmaWeakenSubstEnv cn =
  return (Coq.ID $ "weaken_subst_" ++ cnId cn)

setLemmaWeakenSubstEnv :: Elab m => m [Coq.Identifier]
setLemmaWeakenSubstEnv = getEnvCtors >>= traverse idLemmaWeakenSubstEnv

idLemmaSubstEnvSubstHvl :: Elab m => EnvTypeName -> NamespaceTypeName -> m Coq.Identifier
idLemmaSubstEnvSubstHvl etn ntn = do
  cn <- getEnvCtorName etn ntn
  Coq.ID substEnv <- idTypeSubstEnv cn
  Coq.ID substHvl <- idTypeSubstHvl ntn

  return (Coq.ID $ substEnv ++ "_" ++ substHvl)

setLemmaSubstEnvSubstHvl :: Elab m => m [Coq.Identifier]
setLemmaSubstEnvSubstHvl = do
  envCtors <- M.toList . meNamespaceEnvCtor <$> getMetaEnvironments
  sequenceA [ idLemmaSubstEnvSubstHvl etn ntn | (ntn, (etn, _)) <- envCtors ]

{-------------------------------------------------------------------------------
   ___ _    _  __ _     ___             _   _
  / __| |_ (_)/ _| |_  | __|  _ _ _  __| |_(_)___ _ _
  \__ \ ' \| |  _|  _| | _| || | ' \/ _|  _| / _ \ ' \
  |___/_||_|_|_|  \__| |_| \_,_|_||_\__|\__|_\___/_||_|

-------------------------------------------------------------------------------}

idLemmaStabilityShiftGroup :: Elab m => NamespaceTypeName -> FunGroupName -> m Coq.Identifier
idLemmaStabilityShiftGroup ntn (FGN s) = do
  sr <- getShiftRoot ntn
  return (Coq.ID $ "stability_" ++ sr ++ "_" ++ s)

idLemmaStabilityShift :: Elab m => NamespaceTypeName -> FunName -> m Coq.Identifier
idLemmaStabilityShift ntn fn = do
  sr <- getShiftRoot ntn
  return (Coq.ID $ "stability_" ++ sr ++ "_" ++ fnId fn)

setLemmaStabilityShift' :: Elab m => FunName -> SortTypeName -> m [Coq.Identifier]
setLemmaStabilityShift' fn stn = do
  ntns <- getSortNamespaceDependencies stn
  sequenceA [ idLemmaStabilityShift ntn fn | ntn <- ntns ]

setLemmaStabilityShift :: Elab m => m [Coq.Identifier]
setLemmaStabilityShift = do
  fns <- M.toList . meFunType <$> getMetaEnvironments
  concat <$> sequenceA [ setLemmaStabilityShift' fn stn | (fn,(stn,_)) <- fns ]

idLemmaStabilityWeaken :: Elab m => FunName -> m Coq.Identifier
idLemmaStabilityWeaken fn =
  return (Coq.ID $ "stability_weaken_" ++ fnId fn)

setLemmaStabilityWeaken :: Elab m => m [Coq.Identifier]
setLemmaStabilityWeaken = do
  fns <- M.toList . meFunType <$> getMetaEnvironments
  sequenceA [ idLemmaStabilityWeaken fn | (fn,_) <- fns ]

idLemmaStabilitySubstGroup :: Elab m => NamespaceTypeName -> FunGroupName -> m Coq.Identifier
idLemmaStabilitySubstGroup ntn (FGN s) = do
  sr <- getSubstRoot ntn
  return (Coq.ID $ "stability_" ++ sr ++ "_" ++ s)

idLemmaStabilitySubst :: Elab m => NamespaceTypeName -> FunName -> m Coq.Identifier
idLemmaStabilitySubst ntn fn = do
  sr <- getSubstRoot ntn
  return (Coq.ID $ "stability_" ++ sr ++ "_" ++ fnId fn)

setLemmaStabilitySubst' :: Elab m => FunName -> SortTypeName -> m [Coq.Identifier]
setLemmaStabilitySubst' fn stn = do
  ntns <- getSortNamespaceDependencies stn
  sequenceA [ idLemmaStabilitySubst ntn fn | ntn <- ntns ]

setLemmaStabilitySubst :: Elab m => m [Coq.Identifier]
setLemmaStabilitySubst = do
  fns <- M.toList . meFunType <$> getMetaEnvironments
  concat <$> sequenceA [ setLemmaStabilitySubst' fn stn | (fn,(stn,_)) <- fns ]

{-------------------------------------------------------------------------------
   ___ _    _  __ _      ___
  / __| |_ (_)/ _| |_   / __|___ _ __  _ __
  \__ \ ' \| |  _|  _| | (__/ _ \ '  \| '  \
  |___/_||_|_|_|  \__|  \___\___/_|_|_|_|_|_|

-------------------------------------------------------------------------------}

idLemmaShiftIndexCommInd :: Elab m => NamespaceTypeName -> m Coq.Identifier
idLemmaShiftIndexCommInd ntn = do
  Coq.ID s <- idFunctionShiftIndex ntn
  return (Coq.ID $ s ++ "_" ++ s ++ "0_comm_ind")

idGroupLemmaShiftCommInd :: Elab m =>
  NamespaceTypeName -> NamespaceTypeName -> SortGroupTypeName ->
  m Coq.Identifier
idGroupLemmaShiftCommInd ntn1 ntn2 (SGTN g) = do
  s1 <- getShiftRoot ntn1
  s2 <- getShiftRoot ntn2
  return (Coq.ID $ s1 ++ "_" ++ s2 ++ "0_" ++ g ++ "_comm_ind")

idLemmaShiftCommInd :: Elab m =>
  NamespaceTypeName -> NamespaceTypeName -> SortTypeName ->
  m Coq.Identifier
idLemmaShiftCommInd ntn1 ntn2 (STN _loc g) = do
  s1 <- getShiftRoot ntn1
  s2 <- getShiftRoot ntn2
  return (Coq.ID $ s1 ++ "_" ++ s2 ++ "0_" ++ g ++ "_comm_ind")

idLemmaShiftComm :: Elab m =>
  NamespaceTypeName -> NamespaceTypeName -> SortTypeName ->
  m Coq.Identifier
idLemmaShiftComm ntn1 ntn2 (STN _loc g) = do
  s1 <- getShiftRoot ntn1
  s2 <- getShiftRoot ntn2
  return (Coq.ID $ s1 ++ "_" ++ s2 ++ "0_" ++ g ++ "_comm")

setLemmaShiftComm :: Elab m => m [Coq.Identifier]
setLemmaShiftComm = do
  deps <- meSortNamespaceDeps <$> getMetaEnvironments
  sequenceA
    [ idLemmaShiftComm ntn1 ntn2 stn
    | (stn,ntns) <- M.toList deps, ntn1 <- ntns, ntn2 <- ntns
    ]

{-------------------------------------------------------------------------------
   ___      _       _     ___ _    _  __ _     ___      __ _        _   _
  / __|_  _| |__ __| |_  / __| |_ (_)/ _| |_  | _ \___ / _| |___ __| |_(_)___ _ _
  \__ \ || | '_ (_-<  _| \__ \ ' \| |  _|  _| |   / -_)  _| / -_) _|  _| / _ \ ' \
  |___/\_,_|_.__/__/\__| |___/_||_|_|_|  \__| |_|_\___|_| |_\___\__|\__|_\___/_||_|

-------------------------------------------------------------------------------}

idLemmaSubstIndexShiftIndexReflectionInd ::
  Elab m => NamespaceTypeName -> m Coq.Identifier
idLemmaSubstIndexShiftIndexReflectionInd ntn = do
  Coq.ID subst <- idFunctionSubstIndex ntn
  Coq.ID shift <- idFunctionShiftIndex ntn
  return (Coq.ID $ subst ++ "0_" ++ shift ++ "0_reflection_ind")

idGroupLemmaSubstShiftReflectionInd :: Elab m =>
  NamespaceTypeName -> SortGroupTypeName ->
  m Coq.Identifier
idGroupLemmaSubstShiftReflectionInd ntn (SGTN g) = do
  shift <- getShiftRoot ntn
  subst <- getSubstRoot ntn
  return (Coq.ID $ subst ++ "0_" ++ shift ++ "0_" ++ g ++ "_reflection_ind")

idLemmaSubstShiftReflectionInd :: Elab m =>
  NamespaceTypeName -> SortTypeName ->
  m Coq.Identifier
idLemmaSubstShiftReflectionInd ntn (STN _loc g) = do
  shift <- getShiftRoot ntn
  subst <- getSubstRoot ntn
  return (Coq.ID $ subst ++ "0_" ++ shift ++ "0_" ++ g ++ "_reflection_ind")

idLemmaSubstShiftReflection :: Elab m =>
  NamespaceTypeName -> SortTypeName ->
  m Coq.Identifier
idLemmaSubstShiftReflection ntn stn = do
  Coq.ID shift <- idFunctionShift ntn stn
  Coq.ID subst <- idFunctionSubst ntn stn
  return (Coq.ID $ subst ++ "0_" ++ shift ++ "0_reflection")

setLemmaSubstShiftReflection :: Elab m => m [Coq.Identifier]
setLemmaSubstShiftReflection = do
  deps <- meSortNamespaceDeps <$> getMetaEnvironments
  sequenceA
    [ idLemmaSubstShiftReflection ntn stn
    | (stn,ntns) <- M.toList deps, ntn <- ntns
    ]

{-------------------------------------------------------------------------------
   ___ _    _  __ _     ___      _       _      ___
  / __| |_ (_)/ _| |_  / __|_  _| |__ __| |_   / __|___ _ __  _ __
  \__ \ ' \| |  _|  _| \__ \ || | '_ (_-<  _| | (__/ _ \ '  \| '  \
  |___/_||_|_|_|  \__| |___/\_,_|_.__/__/\__|  \___\___/_|_|_|_|_|_|

-------------------------------------------------------------------------------}

idLemmaShiftSubstIndexCommInd ::
  Elab m => NamespaceTypeName -> NamespaceTypeName -> m Coq.Identifier
idLemmaShiftSubstIndexCommInd ntna ntnb = do
  (stnb,_)   <- getNamespaceCtor ntnb
  Coq.ID shift <- idFunctionShift ntna stnb
  Coq.ID subst <- idFunctionSubstIndex ntnb
  return (Coq.ID $ shift ++ "_" ++ subst ++ "0_comm_ind")

idGroupLemmaShiftSubstCommInd :: Elab m =>
  NamespaceTypeName -> NamespaceTypeName -> SortGroupTypeName ->
  m Coq.Identifier
idGroupLemmaShiftSubstCommInd ntna ntnb (SGTN g) = do
  shift <- getShiftRoot ntna
  subst <- getSubstRoot ntnb
  return (Coq.ID $ shift ++ "_" ++ subst ++ "0_" ++ g ++ "_comm_ind")

idLemmaShiftSubstCommInd :: Elab m =>
  NamespaceTypeName -> NamespaceTypeName -> SortTypeName ->
  m Coq.Identifier
idLemmaShiftSubstCommInd ntna ntnb (STN _loc g) = do
  shift <- getShiftRoot ntna
  subst <- getSubstRoot ntnb
  return (Coq.ID $ shift ++ "_" ++ subst ++ "0_" ++ g ++ "_comm_ind")

idLemmaShiftSubstComm :: Elab m =>
  NamespaceTypeName -> NamespaceTypeName -> SortTypeName ->
  m Coq.Identifier
idLemmaShiftSubstComm ntna ntnb stn = do
  Coq.ID shift <- idFunctionShift ntna stn
  Coq.ID subst <- idFunctionSubst ntnb stn
  return (Coq.ID $ shift ++ "_" ++ subst ++ "0_comm")

setLemmaShiftSubstComm :: Elab m => m [Coq.Identifier]
setLemmaShiftSubstComm = do
  deps <- meSortNamespaceDeps <$> getMetaEnvironments
  sequenceA
    [ idLemmaShiftSubstComm ntn1 ntn2 stn
    | (stn,ntns) <- M.toList deps, ntn1 <- ntns, ntn2 <- ntns
    ]

{-------------------------------------------------------------------------------
   ___      _       _     ___ _    _  __ _      ___
  / __|_  _| |__ __| |_  / __| |_ (_)/ _| |_   / __|___ _ __  _ __
  \__ \ || | '_ (_-<  _| \__ \ ' \| |  _|  _| | (__/ _ \ '  \| '  \
  |___/\_,_|_.__/__/\__| |___/_||_|_|_|  \__|  \___\___/_|_|_|_|_|_|

-------------------------------------------------------------------------------}

idLemmaSubstShiftIndexCommInd ::
  Elab m => NamespaceTypeName -> NamespaceTypeName -> m Coq.Identifier
idLemmaSubstShiftIndexCommInd ntna ntnb = do
  (stna,_)   <- getNamespaceCtor ntna
  Coq.ID subst <- idFunctionSubstIndex ntna
  Coq.ID shift <- idFunctionShift ntnb stna
  return (Coq.ID $ subst ++ "_" ++ shift ++ "0_comm_ind")

idGroupLemmaSubstShiftCommInd :: Elab m =>
  NamespaceTypeName -> NamespaceTypeName -> SortGroupTypeName ->
  m Coq.Identifier
idGroupLemmaSubstShiftCommInd ntna ntnb (SGTN g) = do
  subst <- getSubstRoot ntna
  shift <- getShiftRoot ntnb
  return (Coq.ID $ subst ++ "_" ++ shift ++ "0_" ++ g ++ "_comm_ind")

idLemmaSubstShiftCommInd :: Elab m =>
  NamespaceTypeName -> NamespaceTypeName -> SortTypeName ->
  m Coq.Identifier
idLemmaSubstShiftCommInd ntna ntnb (STN _loc g) = do
  subst <- getSubstRoot ntna
  shift <- getShiftRoot ntnb
  return (Coq.ID $ subst ++ "_" ++ shift ++ "0_" ++ g ++ "_comm_ind")

idLemmaSubstShiftComm :: Elab m =>
  NamespaceTypeName -> NamespaceTypeName -> SortTypeName ->
  m Coq.Identifier
idLemmaSubstShiftComm ntna ntnb stn = do
  Coq.ID subst <- idFunctionSubst ntna stn
  Coq.ID shift <- idFunctionShift ntnb stn
  return (Coq.ID $ subst ++ "_" ++ shift ++ "0_comm")

setLemmaSubstShiftComm :: Elab m => m [Coq.Identifier]
setLemmaSubstShiftComm = do
  deps <- meSortNamespaceDeps <$> getMetaEnvironments
  sequenceA
    [ idLemmaSubstShiftComm ntn1 ntn2 stn
    | (stn,ntns) <- M.toList deps, ntn1 <- ntns, ntn2 <- ntns
    ]

{-------------------------------------------------------------------------------
   ___      _       _     ___      _       _      ___
  / __|_  _| |__ __| |_  / __|_  _| |__ __| |_   / __|___ _ __  _ __
  \__ \ || | '_ (_-<  _| \__ \ || | '_ (_-<  _| | (__/ _ \ '  \| '  \
  |___/\_,_|_.__/__/\__| |___/\_,_|_.__/__/\__|  \___\___/_|_|_|_|_|_|

-------------------------------------------------------------------------------}

idLemmaSubstSubstIndexCommRightInd ::
  Elab m => NamespaceTypeName -> NamespaceTypeName -> m Coq.Identifier
idLemmaSubstSubstIndexCommRightInd ntna ntnb = do
  stnb   <- getSortOfNamespace ntnb
  Coq.ID substa <- idFunctionSubst ntna stnb
  Coq.ID substb <- idFunctionSubstIndex ntnb
  return (Coq.ID $ substa ++ "_" ++ substb ++ "0_commright_ind")

idLemmaSubstSubstIndexCommLeftInd ::
  Elab m => NamespaceTypeName -> NamespaceTypeName -> m Coq.Identifier
idLemmaSubstSubstIndexCommLeftInd ntna ntnb = do
  stnb   <- getSortOfNamespace ntnb
  Coq.ID substa <- idFunctionSubst ntna stnb
  Coq.ID substb <- idFunctionSubstIndex ntnb
  return (Coq.ID $ substa ++ "_" ++ substb ++ "0_commleft_ind")

idGroupLemmaSubstSubstCommInd :: Elab m =>
  NamespaceTypeName -> NamespaceTypeName -> SortGroupTypeName ->
  m Coq.Identifier
idGroupLemmaSubstSubstCommInd ntna ntnb (SGTN g) = do
  subst <- getSubstRoot ntna
  subst2 <- getSubstRoot ntnb
  return (Coq.ID $ subst ++ "_" ++ subst2 ++ "0_" ++ g ++ "_comm_ind")

idLemmaSubstSubstCommInd :: Elab m =>
  NamespaceTypeName -> NamespaceTypeName -> SortTypeName ->
  m Coq.Identifier
idLemmaSubstSubstCommInd ntna ntnb (STN _loc g) = do
  subst <- getSubstRoot ntna
  subst2 <- getSubstRoot ntnb
  return (Coq.ID $ subst ++ "_" ++ subst2 ++ "0_" ++ g ++ "_comm_ind")

idLemmaSubstSubstComm :: Elab m =>
  NamespaceTypeName -> NamespaceTypeName -> SortTypeName ->
  m Coq.Identifier
idLemmaSubstSubstComm ntna ntnb stn = do
  Coq.ID subst <- idFunctionSubst ntna stn
  Coq.ID subst2 <- idFunctionSubst ntnb stn
  return (Coq.ID $ subst ++ "_" ++ subst2 ++ "0_comm")

setLemmaSubstSubstComm :: Elab m => m [Coq.Identifier]
setLemmaSubstSubstComm = do
  deps <- meSortNamespaceDeps <$> getMetaEnvironments
  sequenceA
    [ idLemmaSubstSubstComm ntn ntn stn
    | (stn,ntns) <- M.toList deps, ntn <- ntns
    ]

{-------------------------------------------------------------------------------
   ___      _       _     ___      _                _
  / __|_  _| |__ __| |_  / __|_  _| |__  ___ _ _ __| |
  \__ \ || | '_ (_-<  _| \__ \ || | '_ \/ _ \ '_/ _` |
  |___/\_,_|_.__/__/\__| |___/\_,_|_.__/\___/_| \__,_|

-------------------------------------------------------------------------------}

idGroupLemmaSubstSubordInd :: Elab m =>
  NamespaceTypeName -> NamespaceTypeName -> SortGroupTypeName ->
  m Coq.Identifier
idGroupLemmaSubstSubordInd ntna (NTN _loc ntnb) (SGTN g) = do
  subst <- getSubstRoot ntna
  return (Coq.ID $ subst ++ "_" ++ ntnb ++ "_" ++ g ++ "_ind")

idLemmaSubstSubordInd :: Elab m =>
  NamespaceTypeName -> NamespaceTypeName -> SortTypeName ->
  m Coq.Identifier
idLemmaSubstSubordInd ntna (NTN _locNtnb ntnb) (STN _locStn g) = do
  subst <- getSubstRoot ntna
  return (Coq.ID $ subst ++ "_" ++ ntnb ++ "_" ++ g ++ "_ind")

idLemmaSubstSubord :: Elab m =>
  NamespaceTypeName -> NamespaceTypeName -> SortTypeName ->
  m Coq.Identifier
idLemmaSubstSubord ntna (NTN _loc ntnb) stn = do
  Coq.ID subst <- idFunctionSubst ntna stn
  return (Coq.ID $ subst ++ "_" ++ ntnb)

setLemmaSubstSubord :: Elab m => m [Coq.Identifier]
setLemmaSubstSubord = do
  ntns <- getNamespaces
  allDeps <- meSortNamespaceDeps <$> getMetaEnvironments
  concat <$> sequenceA
    [ do
        (stna,_) <- getNamespaceCtor ntna
        depsa <- getSortNamespaceDependencies stna
        sequenceA
          [ idLemmaSubstSubord ntna ntnb stn
          | ntnb <- ntns \\ depsa
          ]
    | (stn,deps) <- M.toList allDeps
    , ntna <- deps
    ]

{-------------------------------------------------------------------------------
   ___ _
  / __(_)______
  \__ \ |_ / -_)
  |___/_/__\___|

-------------------------------------------------------------------------------}

idFunctionSize :: Elab m => SortTypeName -> m Coq.Identifier
idFunctionSize (STN _loc stn) =
  return (Coq.ID $ "size_" ++ stn)

idGroupLemmaShiftSize :: Elab m =>
  NamespaceTypeName -> SortGroupTypeName ->
  m Coq.Identifier
idGroupLemmaShiftSize ntn (SGTN g) = do
  shift <- getShiftRoot ntn
  return (Coq.ID $ shift ++ "_size_" ++ g)

idLemmaShiftSize :: Elab m =>
  NamespaceTypeName -> SortTypeName ->
  m Coq.Identifier
idLemmaShiftSize ntn (STN _loc g) = do
  shift <- getShiftRoot ntn
  return (Coq.ID $ shift ++ "_size_" ++ g)

setLemmaShiftSize :: Elab m => m [Coq.Identifier]
setLemmaShiftSize = do
  deps <- meSortNamespaceDeps <$> getMetaEnvironments
  sequenceA
    [ idLemmaShiftSize ntn stn
    | (stn,ntns) <- M.toList deps, ntn <- ntns
    ]

idLemmaWeakenSize :: Elab m => SortTypeName -> m Coq.Identifier
idLemmaWeakenSize (STN _loc g) =
  return (Coq.ID $ "weaken_size_" ++ g)

setLemmaWeakenSize :: Elab m => m [Coq.Identifier]
setLemmaWeakenSize = getSorts >>= traverse idLemmaWeakenSize

{-------------------------------------------------------------------------------
  __      __        _
  \ \    / /__ __ _| |_____ _ _
   \ \/\/ / -_) _` | / / -_) ' \
    \_/\_/\___\__,_|_\_\___|_||_|

-------------------------------------------------------------------------------}

idLemmaWeakenShift :: Elab m => NamespaceTypeName -> SortTypeName -> m Coq.Identifier
idLemmaWeakenShift ntn stn = do
  Coq.ID shift  <- idFunctionShift ntn stn
  Coq.ID weaken <- idFunctionWeakenTerm stn
  return (Coq.ID $ weaken ++ "_" ++ shift)

setLemmaWeakenShift :: Elab m => m [Coq.Identifier]
setLemmaWeakenShift = do
  deps <- meSortNamespaceDeps <$> getMetaEnvironments
  sequenceA
    [ idLemmaWeakenShift ntn stn
    | (stn,ntns) <- M.toList deps, ntn <- ntns
    ]

idLemmaWeakenSubst :: Elab m => NamespaceTypeName -> SortTypeName -> m Coq.Identifier
idLemmaWeakenSubst ntn stn = do
  Coq.ID subst  <- idFunctionSubst ntn stn
  Coq.ID weaken <- idFunctionWeakenTerm stn
  return (Coq.ID $ weaken ++ "_" ++ subst)

setLemmaWeakenSubst :: Elab m => m [Coq.Identifier]
setLemmaWeakenSubst = do
  deps <- meSortNamespaceDeps <$> getMetaEnvironments
  sequenceA
    [ idLemmaWeakenSubst ntn stn
    | (stn,ntns) <- M.toList deps, ntn <- ntns
    ]

idLemmaWeakenAppend :: Elab m => SortTypeName -> m Coq.Identifier
idLemmaWeakenAppend stn = do
  Coq.ID weaken <- idFunctionWeakenTerm stn
  return (Coq.ID $ weaken ++ "_append")

idLemmaInsertLookup' :: Elab m => CtorName -> CtorName -> m Coq.Identifier
idLemmaInsertLookup' icn lcn = do
  Coq.ID insert <- idTypeInsertEnv icn
  Coq.ID lookup <- idTypeLookup lcn
  return (Coq.ID $ insert ++ "_" ++ lookup)

idLemmaInsertLookup :: Elab m =>
  EnvTypeName -> NamespaceTypeName -> NamespaceTypeName -> m Coq.Identifier
idLemmaInsertLookup etn insNtn lkNtn = do
  icn <- getEnvCtorName etn insNtn
  lcn <- getEnvCtorName etn lkNtn

  idLemmaInsertLookup' icn lcn

setLemmaInsertLookup :: Elab m => m [Coq.Identifier]
setLemmaInsertLookup = do
  envCtors <- M.toList . meNamespaceEnvCtor <$> getMetaEnvironments
  let cns = [ cn |(_,(_,cn)) <- envCtors ]
  sequenceA [ idLemmaInsertLookup' icn lcn | icn <- cns, lcn <- cns ]

setLemmaWeakenAppend :: Elab m => m [Coq.Identifier]
setLemmaWeakenAppend = getSorts >>= traverse idLemmaWeakenAppend


{-------------------------------------------------------------------------------

-------------------------------------------------------------------------------}

idFunctionAppendEnv :: Elab m => EnvTypeName -> m Coq.Identifier
idFunctionAppendEnv (ETN _loc etn) = return (Coq.ID ("append" ++ etn))

idFunctionDomainEnv :: Elab m => EnvTypeName -> m Coq.Identifier
idFunctionDomainEnv (ETN _loc etn) = return (Coq.ID ("domain" ++ etn))

idFunctionShiftEnv :: Elab m => NamespaceTypeName -> EnvTypeName -> m Coq.Identifier
idFunctionShiftEnv ntn (ETN _loc etn) = do
  sr <- getShiftRoot ntn
  return (Coq.ID $ sr ++ etn)

idFunctionSubstEnv :: Elab m => NamespaceTypeName -> EnvTypeName -> m Coq.Identifier
idFunctionSubstEnv ntn (ETN _loc etn) = do
  sr <- getSubstRoot ntn
  return (Coq.ID $ sr ++ etn)

idLemmaAppendEnvAssoc :: Elab m => EnvTypeName -> m Coq.Identifier
idLemmaAppendEnvAssoc etn = do
  Coq.ID append <- idFunctionAppendEnv etn
  return (Coq.ID (append ++ "_assoc"))

setLemmaAppendEnvAssoc :: Elab m => m [Coq.Identifier]
setLemmaAppendEnvAssoc = getEnvironments >>= traverse idLemmaAppendEnvAssoc

idLemmaDomainEnvAppendEnv :: Elab m => EnvTypeName -> m Coq.Identifier
idLemmaDomainEnvAppendEnv etn = do
  Coq.ID length <- idFunctionDomainEnv etn
  Coq.ID append <- idFunctionAppendEnv etn
  return (Coq.ID (length ++ "_" ++ append))

setLemmaDomainEnvAppendEnv :: Elab m => m [Coq.Identifier]
setLemmaDomainEnvAppendEnv = getEnvironments >>= traverse idLemmaDomainEnvAppendEnv

idLemmaDomainEnvShiftEnv :: Elab m => NamespaceTypeName -> EnvTypeName -> m Coq.Identifier
idLemmaDomainEnvShiftEnv ntn etn = do
  Coq.ID length <- idFunctionDomainEnv etn
  Coq.ID shift  <- idFunctionShiftEnv ntn etn
  return (Coq.ID (length ++ "_" ++ shift))

setLemmaDomainEnvShiftEnv :: Elab m => m [Coq.Identifier]
setLemmaDomainEnvShiftEnv = do
  deps <- M.toList . meEnvNamespaceDeps <$> getMetaEnvironments
  sequenceA [ idLemmaDomainEnvShiftEnv ntn etn
           | (etn,ntns) <- deps, ntn <- ntns
           ]

idLemmaDomainEnvSubstEnv :: Elab m => NamespaceTypeName -> EnvTypeName -> m Coq.Identifier
idLemmaDomainEnvSubstEnv ntn etn = do
  Coq.ID length <- idFunctionDomainEnv etn
  Coq.ID subst  <- idFunctionSubstEnv ntn etn
  return (Coq.ID (length ++ "_" ++ subst))

setLemmaDomainEnvSubstEnv :: Elab m => m [Coq.Identifier]
setLemmaDomainEnvSubstEnv = do
  deps <- M.toList . meEnvNamespaceDeps <$> getMetaEnvironments
  sequenceA [ idLemmaDomainEnvSubstEnv ntn etn
           | (etn,ntns) <- deps, ntn <- ntns
           ]

idLemmaShiftEnvAppendEnv :: Elab m => NamespaceTypeName -> EnvTypeName -> m Coq.Identifier
idLemmaShiftEnvAppendEnv ntn etn = do
  Coq.ID shift  <- idFunctionShiftEnv ntn etn
  Coq.ID append <- idFunctionAppendEnv etn
  return (Coq.ID (shift ++ "_" ++ append))

setLemmaShiftEnvAppendEnv :: Elab m => m [Coq.Identifier]
setLemmaShiftEnvAppendEnv = do
  deps <- M.toList . meEnvNamespaceDeps <$> getMetaEnvironments
  sequenceA [ idLemmaShiftEnvAppendEnv ntn etn
           | (etn,ntns) <- deps, ntn <- ntns
           ]

idLemmaSubstEnvAppendEnv :: Elab m => NamespaceTypeName -> EnvTypeName -> m Coq.Identifier
idLemmaSubstEnvAppendEnv ntn etn = do
  Coq.ID subst  <- idFunctionSubstEnv ntn etn
  Coq.ID append <- idFunctionAppendEnv etn
  return (Coq.ID (subst ++ "_" ++ append))

setLemmaSubstEnvAppendEnv :: Elab m => m [Coq.Identifier]
setLemmaSubstEnvAppendEnv = do
  deps <- M.toList . meEnvNamespaceDeps <$> getMetaEnvironments
  sequenceA [ idLemmaSubstEnvAppendEnv ntn etn
           | (etn,ntns) <- deps, ntn <- ntns
           ]

idFunctionWeakenEnv :: Elab m => EnvTypeName -> m Coq.Identifier
idFunctionWeakenEnv etn =
  return (Coq.ID $ "weaken" ++ etnId etn)

{-------------------------------------------------------------------------------
  __      __   _ _ ___                     _
  \ \    / /__| | | __|__ _ _ _ __  ___ __| |
   \ \/\/ / -_) | | _/ _ \ '_| '  \/ -_) _` |
    \_/\_/\___|_|_|_|\___/_| |_|_|_\___\__,_|

-------------------------------------------------------------------------------}

idRelationWellFormed :: Elab m => SortTypeName -> m Coq.Identifier
idRelationWellFormed (STN _loc stn) =
  return (Coq.ID $ "wf" ++ stn)

idRelationWellFormedCtor :: Elab m => CtorName -> m Coq.Identifier
idRelationWellFormedCtor cn = do
  stn <- lookupCtorType cn
  return (Coq.ID $ "wf" ++ stnId stn ++ "_" ++ cnId cn)

idLemmaShiftWellFormedIndex :: Elab m => NamespaceTypeName -> NamespaceTypeName -> m Coq.Identifier
idLemmaShiftWellFormedIndex ntna (NTN _loc ntnb) = do
  sr             <- getShiftRoot ntna
  Coq.ID wfindex <- idFunctionWellFormedIndex

  return (Coq.ID $ sr ++ "_" ++ wfindex ++ "_" ++ ntnb)

setLemmaShiftWellFormedIndex :: Elab m => m [Coq.Identifier]
setLemmaShiftWellFormedIndex = do
  ntns <- getNamespaces
  sequenceA
    [ idLemmaShiftWellFormedIndex ntn1 ntn2
    | ntn1 <- ntns, ntn2 <- ntns
    ]

idGroupLemmaShiftWellFormedSort :: Elab m => NamespaceTypeName -> SortGroupTypeName -> m Coq.Identifier
idGroupLemmaShiftWellFormedSort ntn sgtn = do
  sr            <- getShiftRoot ntn
  Coq.ID wfterm <- idRelationWellFormed (STN LocNoWhere $ sgtnId sgtn)

  return (Coq.ID $ sr ++ "_" ++ wfterm)

idLemmaShiftWellFormedSort :: Elab m => NamespaceTypeName -> SortTypeName -> m Coq.Identifier
idLemmaShiftWellFormedSort ntn stn = do
  sr            <- getShiftRoot ntn
  Coq.ID wfterm <- idRelationWellFormed stn

  return (Coq.ID $ sr ++ "_" ++ wfterm)

setLemmaShiftWellFormedSort :: Elab m => m [Coq.Identifier]
setLemmaShiftWellFormedSort = do
  stns <- getSorts
  ntns <- getNamespaces
  sequenceA
    [ idLemmaShiftWellFormedSort ntn stn
    | ntn <- ntns
    , stn <- stns
    ]

idGroupLemmaSubstWellFormedSort :: Elab m => NamespaceTypeName -> SortGroupTypeName -> m Coq.Identifier
idGroupLemmaSubstWellFormedSort ntn sgtn = do
  Coq.ID substhvl <- idTypeSubstHvl ntn
  Coq.ID wfterm   <- idRelationWellFormed (STN LocNoWhere $ sgtnId sgtn)

  return (Coq.ID $ substhvl ++ "_" ++ wfterm)

idLemmaSubstWellFormedSort :: Elab m => NamespaceTypeName -> SortTypeName -> m Coq.Identifier
idLemmaSubstWellFormedSort ntn stn = do
  Coq.ID substhvl <- idTypeSubstHvl ntn
  Coq.ID wfterm   <- idRelationWellFormed stn

  return (Coq.ID $ substhvl ++ "_" ++ wfterm)

setLemmaSubstWellFormedSort :: Elab m => m [Coq.Identifier]
setLemmaSubstWellFormedSort = do
  stns <- getSorts
  ntns <- getNamespaces
  sequenceA
    [ idLemmaSubstWellFormedSort ntn stn
    | ntn <- ntns
    , stn <- stns
    ]

idLemmaWeakenWellFormedSort :: Elab m => SortTypeName -> m Coq.Identifier
idLemmaWeakenWellFormedSort stn = do
  Coq.ID wfterm <- idRelationWellFormed stn

  return (Coq.ID $ "weaken_" ++ wfterm)


setTypeInsertHvl :: Elab m => m [Coq.Identifier]
setTypeInsertHvl = getNamespaces >>= traverse idRelationHVarlistInsert

setTypeSubstHvl :: Elab m => m [Coq.Identifier]
setTypeSubstHvl = getNamespaces >>= traverse idTypeSubstHvl

setLemmaWeakenRelationHVarlistInsert :: Elab m => m [Coq.Identifier]
setLemmaWeakenRelationHVarlistInsert = getNamespaces >>= traverse idLemmaWeakenRelationHVarlistInsert

setInsertEnvInsertHvl :: Elab m => m [Coq.Identifier]
setInsertEnvInsertHvl = do
  envCtors <- M.toList . meNamespaceEnvCtor <$> getMetaEnvironments
  sequenceA [ idLemmaInsertEnvInsertHvl etn ntn | (ntn, (etn, _)) <- envCtors ]

idLemmaWeakenLookup :: Elab m => CtorName -> m Coq.Identifier
idLemmaWeakenLookup cn = do
  Coq.ID lookup <- idTypeLookup cn
  return (Coq.ID $ "weaken_" ++ lookup)

setLemmaWeakenLookup :: Elab m => m [Coq.Identifier]
setLemmaWeakenLookup = do
  envCtors <- M.toList . meNamespaceEnvCtor <$> getMetaEnvironments
  let cns = [ cn |(_,(_,cn)) <- envCtors ]
  sequenceA [ idLemmaWeakenLookup cn | cn <- cns ]


idLemmaWeakenLookupHere :: Elab m => CtorName -> m Coq.Identifier
idLemmaWeakenLookupHere cn = do
  Coq.ID lookup <- idCtorLookupHere cn
  return (Coq.ID $ "weaken_" ++ lookup)

setLemmaWeakenLookupHere :: Elab m => m [Coq.Identifier]
setLemmaWeakenLookupHere = do
  envCtors <- M.toList . meNamespaceEnvCtor <$> getMetaEnvironments
  let cns = [ cn |(_,(_,cn)) <- envCtors ]
  sequenceA [ idLemmaWeakenLookupHere cn | cn <- cns ]



idLemmaSubstEnvLookup' :: Elab m => CtorName -> CtorName -> m Coq.Identifier
idLemmaSubstEnvLookup' scn lcn = do
  Coq.ID subst  <- idTypeSubstEnv scn
  Coq.ID lookup <- idTypeLookup lcn
  return (Coq.ID $ subst ++ "_" ++ lookup)

idLemmaSubstEnvLookup :: Elab m =>
  EnvTypeName -> NamespaceTypeName -> NamespaceTypeName -> m Coq.Identifier
idLemmaSubstEnvLookup etn subNtn lkNtn = do
  scn <- getEnvCtorName etn subNtn
  lcn <- getEnvCtorName etn lkNtn

  idLemmaSubstEnvLookup' scn lcn

setLemmaSubstEnvLookup :: Elab m => m [Coq.Identifier]
setLemmaSubstEnvLookup = do
  envCtors <- M.toList . meNamespaceEnvCtor <$> getMetaEnvironments
  let cns = [ cn |(_,(_,cn)) <- envCtors ]
  sequenceA [ idLemmaSubstEnvLookup' scn lcn
           | scn <- cns , lcn <- cns , scn /= lcn ]

idLemmaLookupWellformedData :: Elab m => CtorName -> m Coq.Identifier
idLemmaLookupWellformedData cn = do
  Coq.ID lk <- idTypeLookup cn
  return (Coq.ID $ lk ++ "_wf")

setLemmaLookupWellformedData :: Elab m => m [Coq.Identifier]
setLemmaLookupWellformedData = do
  allCtors <- concat . M.elems . meEnvCtors <$> getMetaEnvironments
  sequenceA [ idLemmaLookupWellformedData cn
           | EnvCtorCons cn _ fields _ <- allCtors
           , not (null fields)
           ]

setRelationWellFormed :: Elab m => m [Coq.Identifier]
setRelationWellFormed = getSorts >>= traverse idRelationWellFormed

idFunctionSubHvl :: Elab m => [NamespaceTypeName] -> m Coq.Identifier
idFunctionSubHvl ntns =
  return (Coq.ID $ "subhvl_" ++ intercalate "_" (map ntnId ntns))

idLemmaSubHvlAppend :: Elab m => [NamespaceTypeName] -> m Coq.Identifier
idLemmaSubHvlAppend ntns = do
  Coq.ID subhvl <- idFunctionSubHvl ntns
  return (Coq.ID $ subhvl ++ "_append")

idLemmaWellFormedStrengthen :: Elab m =>
  SortTypeName -> [NamespaceTypeName] -> m Coq.Identifier
idLemmaWellFormedStrengthen stn ntns = do
  Coq.ID wf <- idRelationWellFormed stn
  Coq.ID subhvl <- idFunctionSubHvl ntns
  return (Coq.ID $ wf ++ "_strengthen_" ++ subhvl)

idLemmaShiftRelation :: Elab m =>
  EnvTypeName -> NamespaceTypeName -> RelationTypeName -> m Coq.Identifier
idLemmaShiftRelation etn ntn (RTN _loc rtn) = do
  icn <- getEnvCtorName etn ntn
  Coq.ID insert <- idTypeInsertEnv icn
  return (Coq.ID $ insert ++ "_" ++ rtn)

setLemmaShiftRelation :: Elab m => m [Coq.Identifier]
setLemmaShiftRelation = do
  rtnEtns <- M.toList . meRelationEnvTypeNames <$> getMetaEnvironments
  lemmass <- for rtnEtns $ \(rtn,etn) -> do
    ntns <- getEnvNamespaces
    sequenceA [idLemmaShiftRelation etn ntn rtn | ntn <- ntns]
  return (concat lemmass)

idLemmaWeakenRelation :: Elab m =>
  RelationTypeName -> m Coq.Identifier
idLemmaWeakenRelation rtn =
  return (Coq.ID $ "weaken_" ++ rtnId rtn)

idLemmaRelationWellFormed :: Elab m =>
  RelationTypeName -> Int -> m Coq.Identifier
idLemmaRelationWellFormed rtn i =
  return (Coq.ID $ rtnId rtn ++ "_wf_" ++ show i)

idLemmaWellFormedInversion :: Elab m =>
  SortTypeName -> CtorName -> Int -> m Coq.Identifier
idLemmaWellFormedInversion stn cn i = do
  Coq.ID wf <- idRelationWellFormed stn
  return (Coq.ID $ "inversion_" ++ wf ++ "_" ++ cnId cn ++ "_" ++ show i)

idLemmaDomainOutput :: Elab m =>
  RelationTypeName -> FunName -> m Coq.Identifier
idLemmaDomainOutput rtn fn =
  return (Coq.ID $ "domain_" ++ rtnId rtn ++ "_" ++ fnId fn)

idLemmaRelationCast :: Elab m =>
  RelationTypeName -> m Coq.Identifier
idLemmaRelationCast rtn =
  return (Coq.ID $ rtnId rtn ++ "_cast")

idLemmaWellFormedTermCast :: Elab m =>
  SortTypeName -> m Coq.Identifier
idLemmaWellFormedTermCast stn = do
  Coq.ID wf <- idRelationWellFormed stn
  return (Coq.ID $ wf ++ "_cast")

idClassObligationVar :: Elab m =>
  EnvTypeName -> NamespaceTypeName -> m Coq.Identifier
idClassObligationVar etn ntn =
  return (Coq.ID $ "Obligation_" ++ etnId etn ++ "_var_" ++ ntnId ntn)

idMethodObligationVar :: Elab m =>
  EnvTypeName -> NamespaceTypeName -> m Coq.Identifier
idMethodObligationVar etn ntn =
  return (Coq.ID $ etnId etn ++ "_var_" ++ ntnId ntn)

idInstObligationVar :: Elab m =>
  EnvTypeName -> NamespaceTypeName -> m Coq.Identifier
idInstObligationVar etn ntn =
  return (Coq.ID $ "obligation_" ++ etnId etn ++ "_var_" ++ ntnId ntn)


idClassObligationReg :: Elab m =>
  EnvTypeName -> NamespaceTypeName -> RelationTypeName -> m Coq.Identifier
idClassObligationReg etn ntn rtn =
  return (Coq.ID $ "Obligation_" ++ etnId etn ++ "_reg_" ++ rtnId rtn)

idMethodObligationReg :: Elab m =>
  EnvTypeName -> NamespaceTypeName -> CtorName -> m Coq.Identifier
idMethodObligationReg etn ntn cn =
  return (Coq.ID $ etnId etn ++ "_reg_" ++ cnId cn)

idInstObligationReg :: Elab m =>
  EnvTypeName -> NamespaceTypeName -> RelationTypeName -> m Coq.Identifier
idInstObligationReg etn ntn rtn =
  return (Coq.ID $ "obligation_" ++ etnId etn ++ "_reg_" ++ rtnId rtn)

idLemmaSubstRelation :: Elab m =>
  EnvTypeName -> NamespaceTypeName -> RelationTypeName -> m Coq.Identifier
idLemmaSubstRelation etn ntn (RTN _loc rtn) = do
  scn <- getEnvCtorName etn ntn
  Coq.ID subst <- idTypeSubstEnv scn
  return (Coq.ID $ subst ++ "_" ++ rtn)

setLemmaSubstRelation :: Elab m => m [Coq.Identifier]
setLemmaSubstRelation = do
  rtnEtns <- M.toList . meRelationEnvTypeNames <$> getMetaEnvironments
  lemmass <- for rtnEtns $ \(rtn,etn) -> do
    ntns <- getEnvNamespaces
    sequenceA [idLemmaSubstRelation etn ntn rtn | ntn <- ntns]
  return (concat lemmass)
