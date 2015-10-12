{-# LANGUAGE MultiParamTypeClasses #-}

module KnotCore.Elaboration.Core (
  module KnotCore.Elaboration.Core,
  module KnotCore.Elaboration.Fresh,
  module KnotCore.Elaboration.Identifiers,
  module KnotCore.Elaboration.Monad,
  module KnotCore.Elaboration.Names,
  module KnotCore.Syntax,
  module KnotCore.Environment
) where

import Control.Applicative

import Data.Maybe (catMaybes)

import KnotCore.Syntax
import KnotCore.Environment
import KnotCore.Elaboration.Fresh
import KnotCore.Elaboration.Identifiers
import KnotCore.Elaboration.Monad
import KnotCore.Elaboration.Names

import qualified Coq.StdLib as Coq
import qualified Coq.Syntax as Coq

--    _           _ _ _
--   /_\ _  ___ _(_) (_)__ _ _ _ _  _
--  / _ \ || \ \ / | | / _` | '_| || |
-- /_/ \_\_,_/_\_\_|_|_\__,_|_|  \_, |
--                               |__/

data HVarlist
  = HV0
  | HVS NamespaceTypeName HVarlist
  | HVVar HVarlistVar
  | HVCall [NamespaceTypeName] FunName STerm
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
  = SVar SubtreeVar
  | SCtorVar CtorName Index
  | SCtorTerm CtorName [STerm]
  | SShift Cutoff STerm
  | SShift' Cutoff STerm
  | SSubst Trace STerm STerm
  | SSubst' Trace STerm STerm
  | SSubstIndex Trace STerm Index
  | SWeaken STerm HVarlist
  deriving (Eq,Ord,Show)

data ETerm
  = EVar EnvVar
  | ECtor CtorName ETerm [STerm]
  | EAppend ETerm ETerm
  | EShift Cutoff ETerm
  | EShift' Cutoff ETerm
  | ESubst Trace STerm ETerm
  | ESubst' Trace STerm ETerm
  deriving (Eq,Ord,Show)

data Lookup
  = Lookup ETerm Index [STerm]
  deriving (Eq,Ord,Show)

data InsertEnv
  = InsertEnv Cutoff ETerm ETerm
  deriving (Eq,Ord,Show)

data SubstEnv
  = SubstEnv ETerm [STerm] STerm Trace ETerm ETerm
  deriving (Eq,Ord,Show)

data Prop
  = PEqTerm STerm STerm
  | PAnd [Prop]
  deriving (Eq,Ord,Show)

data WellFormedIndex
  = WfIndex HVarlist Index
  deriving (Eq,Ord,Show)

data WellFormedTerm
  = WfTerm HVarlist STerm
  deriving (Eq,Ord,Show)

data HVarlistInsertion
  = HVarlistInsertion Cutoff HVarlist HVarlist
  deriving (Eq,Ord,Show)

data SubstHvl
  = SubstHvl HVarlist Trace HVarlist HVarlist
  deriving (Eq,Ord,Show)

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

instance TypeNameOf WellFormedTerm SortTypeName where
  typeNameOf (WfTerm _ s)  = typeNameOf s

instance SortOf Index where
  sortOf (I0 _ stn)    = stn
  sortOf (IS i)        = sortOf i
  sortOf (IVar iv)     = sortOf iv
  sortOf (IWeaken i _) = sortOf i
  sortOf (IShift _ i)  = sortOf i
  sortOf (IShift' _ i) = sortOf i

instance SortOf STerm where
  sortOf (SVar sv)           = sortOf sv
  sortOf (SCtorVar cn _)     = cnSort cn
  sortOf (SCtorTerm cn _)    = cnSort cn
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
  typeNameOf (ECtor _ et _)   = typeNameOf et
  typeNameOf (EAppend et _)   = typeNameOf et
  typeNameOf (EShift _ et)    = typeNameOf et
  typeNameOf (EShift' _ et)   = typeNameOf et
  typeNameOf (ESubst _ _ et)  = typeNameOf et
  typeNameOf (ESubst' _ _ et) = typeNameOf et

instance SortOf WellFormedIndex where
  sortOf (WfIndex _ i) = sortOf i

instance SortOf WellFormedTerm where
  sortOf (WfTerm _ s)  = sortOf s

freshVariable :: Elab m => String -> Coq.Term -> m Coq.Variable
freshVariable nr tm =
  do
    suff <- freshSuffix (NR nr) ""
    return (Coq.Variable (Coq.ID $ nr ++ suff) tm)

class TermLike a where
  toTerm :: Elab m => a -> m Coq.Term

instance TermLike HVarlist where
  toTerm (HV0)                = idCtorHVarlistNil >>= toRef
  toTerm (HVS ntn hvl)        = Coq.TermApp
                                <$> (idCtorHVarlistCons >>= toRef)
                                <*> sequence [idCtorNamespace ntn >>= toRef, toTerm hvl]
  toTerm (HVVar hvv)          = toRef hvv
  toTerm (HVCall _ fn sn)     = Coq.TermApp
                                <$> toRef fn
                                <*> sequence [toTerm sn]
  toTerm (HVAppend hvl1 hvl2) = Coq.TermApp
                                <$> (idAppendHVarlist >>= toRef)
                                <*> sequence [toTerm hvl1, toTerm hvl2]
  toTerm (HVDomainEnv et)     = Coq.TermApp
                                <$> (idFunctionDomainEnv (typeNameOf et) >>= toRef)
                                <*> sequence [toTerm et]

instance TermLike Cutoff where
  toTerm (C0 _)               = idFamilyCutoffZero >>= toRef
  toTerm (CS c)               = Coq.TermApp
                                <$> (idFamilyCutoffSucc >>= toRef)
                                <*> sequence [toTerm c]
  toTerm (CS' ntn c)          = if typeNameOf c == ntn
                                then toTerm (CS c)
                                else toTerm c
  toTerm (CVar cv)            = toRef cv
  toTerm (CWeaken c hvl)      = Coq.TermApp
                                <$> (idFunctionWeakenCutoff (typeNameOf c) >>= toRef)
                                <*> sequence [toTerm c, toTerm hvl]

instance TermLike Index where
  toTerm (I0 _ _)             = idFamilyIndexZero >>= toRef
  toTerm (IS i)               = Coq.TermApp
                                <$> (idFamilyIndexSucc >>= toRef)
                                <*> sequence [toTerm i]
  toTerm (IVar iv)            = toRef iv
  toTerm (IShift c i)         = Coq.TermApp
                                <$> (idFunctionShiftIndex (typeNameOf c) >>= toRef)
                                <*> sequence [toTerm c, toTerm i]
  toTerm (IShift' c i)        = if typeNameOf c == typeNameOf i
                                then toTerm (IShift c i)
                                else toTerm i
  toTerm (IWeaken i hvl)      = Coq.TermApp
                                <$> (idFunctionWeakenIndex (typeNameOf i) >>= toRef)
                                <*> sequence [toTerm i, toTerm hvl]

instance TermLike Trace where
  toTerm (T0 _)               = idFamilyTraceNil >>= toRef
  toTerm (TS ntn c)           = Coq.TermApp
                                <$> (idFamilyTraceCons >>= toRef)
                                <*> sequence [toRef ntn, toTerm c]
  toTerm (TVar cv)            = toRef cv
  toTerm (TWeaken c hvl)      = Coq.TermApp
                                <$> (idFunctionWeakenTrace >>= toRef)
                                <*> sequence [toTerm c, toTerm hvl]

instance TermLike STerm where
  toTerm (SVar sv)            = toRef sv
  toTerm (SCtorVar cn i)      = Coq.TermApp
                                <$> toRef cn
                                <*> sequence [toTerm i]
  toTerm (SCtorTerm cn ss)    = Coq.TermApp
                                <$> toRef cn
                                <*> mapM toTerm ss
  toTerm (SShift c t)         = Coq.TermApp
                                <$> (idFunctionShift (typeNameOf c) (typeNameOf t) >>= toRef)
                                <*> sequence [toTerm c, toTerm t]
  toTerm (SShift' c t)        = do
                                  deps <- getSortNamespaceDependencies (typeNameOf t)
                                  if typeNameOf c `elem` deps
                                    then toTerm (SShift c t)
                                    else toTerm t
  toTerm (SSubst x s t)       = Coq.TermApp
                                <$> (idFunctionSubst (typeNameOf x) (typeNameOf t) >>= toRef)
                                <*> sequence [toTerm x, toTerm s, toTerm t]
  toTerm (SSubst' x s t)      =  do
                                  deps <- getSortNamespaceDependencies (typeNameOf t)
                                  if typeNameOf x `elem` deps
                                    then toTerm (SSubst x s t)
                                    else toTerm t
  toTerm (SSubstIndex x s y)  = Coq.TermApp
                                <$> (idFunctionSubstIndex (typeNameOf y) >>= toRef)
                                <*> sequence [toTerm x, toTerm s, toTerm y]
  toTerm (SWeaken t hvl)      = Coq.TermApp
                                <$> (idFunctionWeakenTerm (typeNameOf t) >>= toRef)
                                <*> sequence [toTerm t, toTerm hvl]

instance TermLike ETerm where
  toTerm (EVar ev)            = toRef ev
  toTerm (ECtor cn et ts)     = Coq.TermApp
                                <$> toRef cn
                                <*> sequence (toTerm et : map toTerm ts)
  toTerm (EAppend et1 et2)    = Coq.TermApp
                                <$> (idFunctionAppendEnv (typeNameOf et1) >>= toRef)
                                <*> sequence [toTerm et1, toTerm et2]
  toTerm (EShift c et)        = Coq.TermApp
                                <$> (idFunctionShiftEnv (typeNameOf c) (typeNameOf et) >>= toRef)
                                <*> sequence [toTerm c, toTerm et]
  toTerm (EShift' c et)       = do
                                  deps <- getEnvNamespaceDependencies (typeNameOf et)
                                  if typeNameOf c `elem` deps
                                    then toTerm (EShift c et)
                                    else toTerm et
  toTerm (ESubst x s et)      = Coq.TermApp
                                <$> (idFunctionSubstEnv (typeNameOf x) (typeNameOf et) >>= toRef)
                                <*> sequence [toTerm x, toTerm s, toTerm et]
  toTerm (ESubst' x s et)     = do
                                  deps <- getEnvNamespaceDependencies (typeNameOf et)
                                  if typeNameOf x `elem` deps
                                    then toTerm (ESubst x s et)
                                    else toTerm et

instance TermLike Lookup where
  toTerm (Lookup et x ts) = do
    cn <- getEnvCtorName (typeNameOf et) (typeNameOf x)
    typeLookup cn et x ts

instance TermLike InsertEnv where
  toTerm (InsertEnv c et1 et2) = do
    cn <- getEnvCtorName (typeNameOf et1) (typeNameOf c)
    typeInsertEnv cn c et1 et2

instance TermLike SubstEnv where
  toTerm (SubstEnv e ts t x e1 e2) = do
    cn <- getEnvCtorName (typeNameOf e) (typeNameOf x)
    typeSubstEnv cn e ts t x e1 e2

instance TermLike Prop where
  toTerm (PEqTerm l r) = Coq.TermEq <$> toTerm l <*> toTerm r
  toTerm (PAnd ps)     = Coq.TermAnd <$> mapM toTerm ps

instance TermLike WellFormedIndex where
  toTerm (WfIndex h i) = Coq.TermApp
                         <$> (idFunctionWellFormedIndex >>= toRef)
                         <*> sequence [toTerm h, toTerm i]

instance TermLike WellFormedTerm where
  toTerm (WfTerm h s)  = Coq.TermApp
                         <$> (idRelationWellFormed (sortOf s) >>= toRef)
                         <*> sequence [toTerm h, toTerm s]

instance TermLike HVarlistInsertion where
  toTerm (HVarlistInsertion c h1 h2) =
    Coq.TermApp
    <$> (idRelationHVarlistInsert (typeNameOf c) >>= toRef)
    <*> sequence [toTerm c, toTerm h1, toTerm h2]

instance TermLike SubstHvl where
  toTerm (SubstHvl h x h1 h2) =
    Coq.TermApp
    <$> (idTypeSubstHvl (typeNameOf x) >>= toRef)
    <*> sequence [toTerm h, toTerm x, toTerm h1, toTerm h2]

typeLookup :: Elab m => CtorName -> ETerm -> Index -> [STerm] -> m Coq.Term
typeLookup cn e x ts =
  Coq.TermApp
  <$> (idTypeLookup cn >>= toRef)
  <*> sequence (toTerm e:toTerm x:map toTerm ts)

typeInsertEnv :: Elab m => CtorName -> Cutoff -> ETerm -> ETerm -> m Coq.Term
typeInsertEnv cn c e1 e2 =
  Coq.TermApp
  <$> (idTypeInsertEnv cn >>= toRef)
  <*> sequence [toTerm c, toTerm e1, toTerm e2]

typeSubstEnv :: Elab m => CtorName -> ETerm -> [STerm] -> STerm -> Trace -> ETerm -> ETerm -> m Coq.Term
typeSubstEnv cn e ts t x e1 e2 =
  Coq.TermApp
  <$> (idTypeSubstEnv cn >>= toRef)
  <*> (sequence $ [toTerm e] ++ map toTerm ts ++ [toTerm t, toTerm x, toTerm e1, toTerm e2])

-- Subtree names
shiftedSubtreeRef :: Elab m => CutoffVar -> SubtreeVar -> m Coq.Term
shiftedSubtreeRef cv sv = do
  let ntn = typeNameOf cv
  deps  <- getSortNamespaceDependencies (typeNameOf sv)
  shift <- idFunctionShift ntn (typeNameOf sv)

  if ntn `elem` deps
    then Coq.TermApp <$> toRef shift <*> sequence [toRef cv, toRef sv]
    else toRef sv

-- Environment type names
nameEnvNil :: Elab m => EnvTypeName -> m Coq.Identifier
nameEnvNil (ETN s) = return (Coq.ID $ s ++ "_nil")

-- Hypothesis
hypothesisIdentifier :: Elab m => Hypothesis -> m Coq.Identifier
hypothesisIdentifier (Hypothesis nr suff) =
  return (Coq.ID $ fromNR nr ++ suff)

hypothesisRef :: Elab m => Hypothesis -> m Coq.Term
hypothesisRef = fmap (Coq.TermQualId . Coq.Ident) . hypothesisIdentifier

{-
eFormula :: Elab m => Maybe EnvVar -> Formula -> m Coq.Term
eFormula (Just en) (FormBinding (RuleBinding mv sts)) =
  do
    (etn,cn) <- getNamespaceEnvCtor (typeNameOf mv)
    rtn      <- lookupTypeName etn cn
    relType  <- toRef rtn
    eidx     <- envVarRef en
    midx     <- toIndex mv >>= toRef
    sids     <- mapM eSymbolicTerm sts
    return (Coq.TermApp relType (eidx:midx:catMaybes sids))
eFormula mbEnvVar (FormJudgement _ rtn _ sts)
  = Coq.TermApp
      <$> toRef rtn
      <*> liftM2 (++)
            (eMbEnvVarRef (mbEnvVar >> mbEnvVar))
            (catMaybes <$> mapM eSymbolicTerm sts)
eFormula Nothing (FormBinding _) = error "eFormula ???"
-}

{-
eJudgement :: Elab m => Maybe EnvVar -> Judgement -> m Coq.Term
eJudgement mbEnvVar (Judgement rtn mbEnv sts) =
  Coq.TermApp
    <$> toRef rtn
    <*> liftM2 (++)
          (eMbEnvVarRef (mbEnv >> mbEnvVar))
          (catMaybes <$> mapM eSymbolicTerm sts)
-}

eSymbolicTerm :: Elab m => SymbolicTerm -> m (Maybe Coq.Term)
eSymbolicTerm (SymBinding _)    = return Nothing
eSymbolicTerm (SymSubtree sn)    = Just <$> toRef sn
eSymbolicTerm (SymEnv en)        = Just <$> toRef en
eSymbolicTerm (SymCtorVar cn mv) = fmap Just $
  Coq.TermApp
    <$> toRef cn
    <*> sequence [ toIndex mv >>= toRef ]
eSymbolicTerm (SymCtorTerm cn fields) = fmap Just $
  Coq.TermApp
    <$> toRef cn
    <*> (catMaybes <$> mapM eSymbolicTerm fields)
eSymbolicTerm (SymSubst _ _ _) = error "NOT_IMPLEMENTED"
--  ___          _           _   _
-- | __|_ ____ _| |_  _ __ _| |_(_)___ _ _
-- | _|\ V / _` | | || / _` |  _| / _ \ ' \
-- |___|\_/\__,_|_|\_,_\__,_|\__|_\___/_||_|

evalVleItem :: VleItem -> HVarlist
evalVleItem (VleBinding _ mv)    = HVS (typeNameOf mv) HV0
evalVleItem (VleCall ntns fn sn) = HVCall ntns fn (SVar sn)

evalBindSpec :: BindSpec -> HVarlist
evalBindSpec []       = HV0
evalBindSpec (vle:bs) = HVAppend (evalVleItem vle) (evalBindSpec bs)

liftCutoffVar :: BindSpec -> CutoffVar -> Cutoff
liftCutoffVar bs cv = CWeaken (CVar cv) (evalBindSpec bs)

liftTraceVar :: BindSpec -> TraceVar -> Trace
liftTraceVar []       cv = TVar cv
liftTraceVar (vle:bs) cv =
  case vle of
    VleBinding _ mv    -> TS (typeNameOf mv) (liftTraceVar bs cv)
    VleCall ntns fn sn -> TWeaken (liftTraceVar bs cv) (HVCall ntns fn (SVar sn))
