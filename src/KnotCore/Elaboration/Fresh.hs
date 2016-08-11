{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

module KnotCore.Elaboration.Fresh
  ( module KnotCore.Elaboration.Fresh
  , module Knot.Env
  , module Knot.Fresh
  ) where

import           Knot.Env
import           Knot.Fresh
import           KnotCore.Elaboration.Monad
import           KnotCore.DeBruijn.Core
import           KnotCore.Syntax

import           Control.Applicative
import           Control.Monad
import qualified Data.Foldable as F
import           Data.Map                   (Map)
import qualified Data.Map                   as M
import           Data.Set                   (Set)
import qualified Data.Set                   as S

--------------------------------------------------------------------------------

class Names a where
  collect :: a -> Set (NameRoot,Suffix)
  rename  :: Map (NameRoot,Suffix) (NameRoot,Suffix) -> a -> a

instance Names a => Names [a] where
  collect  = S.unions . map collect
  rename m = fmap (rename m)

instance Names a => Names (SnocList a) where
  collect  = S.unions . map collect . F.toList
  rename m = fmap (rename m)

instance Names a => Names (Maybe a) where
  collect  = maybe S.empty collect
  rename m = fmap (rename m)

instance (Names a, Names b) => Names (a,b) where
  collect (a,b)= S.union (collect a) (collect b)
  rename m (a,b) = (rename m a, rename m b)

instance Names FunName where
  collect _ = S.empty
  rename _ = id

instance Names FreeVariable where
  collect (FV nr suff _) = S.singleton (nr,suff)
  rename m (FV nr suff ntn) =
    case M.findWithDefault (error "rename@FreeVariable") (nr,suff) m of
      (nr',suff') -> FV nr' suff' ntn

instance Names BindingVariable where
  collect (BV nr suff _) = S.singleton (nr,suff)
  rename m (BV nr suff ntn) =
    case M.findWithDefault (error "rename@BindingVariable") (nr,suff) m of
      (nr',suff') -> BV nr' suff' ntn

instance Names IndexVar where
  collect (IndexVar nr suff _ _) = S.singleton (nr,suff)
  rename m (IndexVar nr suff ntn stn) =
    case M.findWithDefault (error "rename@IndexVar") (nr,suff) m of
      (nr',suff') -> IndexVar nr' suff' ntn stn

instance Names SortVariable where
  collect (SV nr suff _) = S.singleton (nr,suff)
  rename m (SV nr suff stn) =
    case M.findWithDefault (error "rename@SortVariable") (nr,suff) m of
      (nr',suff') -> SV nr' suff' stn

instance Names EnvVariable where
  collect (EV nr suff _) = S.singleton (nr,suff)
  rename m (EV nr suff etn) =
    case M.findWithDefault (error "rename@EnvVar") (nr,suff) m of
      (nr',suff') -> EV nr' suff' etn

instance Names LookupVar where
  collect (LookupVar nr suff se rv sfs) =
    S.unions [S.singleton (nr,suff), collect se, collect rv, collect sfs]
  rename m (LookupVar nr suff se rv sfs) =
    case M.findWithDefault (error "rename@LookupVar") (nr,suff) m of
      (nr',suff') -> LookupVar nr' suff' (rename m se) (rename m rv) (rename m sfs)

instance Names JudgementVariable where
  collect (JV nr suff _rtn) = S.singleton (nr,suff)
  rename m (JV nr suff rtn) =
    case M.findWithDefault (error "rename@JudgementVariable") (nr,suff) m of
      (nr',suff') -> JV nr' suff' rtn

instance Names Hypothesis where
  collect (Hypothesis nr suff)  = S.singleton (nr,suff)
  rename m (Hypothesis nr suff) =
    case M.findWithDefault (error "rename@Hypothesis") (nr,suff) m of
      (nr',suff') -> Hypothesis nr' suff'

instance Names BindSpecItem where
  collect (BsiBinding mv) = collect mv
  collect (BsiCall _ sv)  = collect sv
  rename m (BsiBinding mv) = BsiBinding (rename m mv)
  rename m (BsiCall fn sv) = BsiCall fn (rename m sv)

instance Names (FieldDecl w) where
  collect fieldDecl = case fieldDecl of
    FieldDeclSort sv bs wf   -> S.unions [collect sv, collect bs, collect wf]
    FieldDeclBinding bs mv   -> S.unions [collect bs, collect mv]
    FieldDeclReference fv wf -> S.unions [collect fv, collect wf]
  rename m fieldDecl = case fieldDecl of
    FieldDeclSort sv bs wf   -> FieldDeclSort (rename m sv) (rename m bs) (rename m wf)
    FieldDeclBinding bs mv   -> FieldDeclBinding (rename m bs) (rename m mv)
    FieldDeclReference fv wf -> FieldDeclReference (rename m fv) (rename m wf)

instance Names CtorDecl where
  collect (CtorVar _ mv wf)  = S.unions [collect mv, collect wf]
  collect (CtorReg _ fds) = collect fds
  rename m (CtorVar cn mv wf)   = CtorVar cn (rename m mv) (rename m wf)
  rename m (CtorReg cn  fds) = CtorReg cn (rename m fds)

instance Names EnvCtor where
  collect (EnvCtorNil _)               = S.empty
  collect (EnvCtorCons _ mv svs _)     = S.unions [collect mv, collect svs]
  rename _ (EnvCtorNil cn)             = EnvCtorNil cn
  rename m (EnvCtorCons cn mv svs rtn) =
    EnvCtorCons cn (rename m mv) (rename m svs) rtn

instance Names RelationDecl where
  collect (RelationDecl mbEv _ _ _ _ rules) =
    S.unions [collect mbEv, collect rules]
  rename m rd = rd { relEnv   = rename m (relEnv rd)
                   , relRules = rename m (relRules rd)
                   }

instance Names RuleMetavarBinder where
  collect rmb
   | RuleMetavarSort bs sv hyp pos <- rmb
   = S.unions [collect bs, collect sv, collect hyp, collect pos]
   | RuleMetavarFree mv hyp <- rmb
   = S.unions [collect mv, collect hyp]
   | RuleMetavarBinding bs mv <- rmb
   = S.unions [collect bs, collect mv]
   | RuleMetavarOutput bs ev <- rmb
   = S.unions [collect bs, collect ev]
  rename m rmb
    | RuleMetavarSort bs sv hyp pos <- rmb
    = RuleMetavarSort (rename m bs) (rename m sv) (rename m hyp)
        (rename m pos)
    | RuleMetavarFree mv hyp <- rmb
    = RuleMetavarFree (rename m mv) (rename m hyp)
    | RuleMetavarBinding bs mv <- rmb
    = RuleMetavarBinding (rename m bs) (rename m mv)
    | RuleMetavarOutput bs ev <- rmb
    = RuleMetavarOutput (rename m bs) (rename m ev)

instance Names Rule where
  collect r = case r of
    RuleVar _ rmbs etn fv sfs jm ->
      S.unions [collect rmbs, collect fv, collect sfs, collect jm]
    RuleReg _cn rmbs fmls jm outs ->
      S.unions [collect rmbs, collect fmls, collect jm, collect outs]
  rename m r = case r of
    RuleVar cn rmbs etn fv sfs jm ->
      RuleVar cn (rename m rmbs) etn (rename m fv) (rename m sfs) (rename m jm)
    RuleReg cn rmbs fmls jm outs ->
      RuleReg cn (rename m rmbs) (rename m fmls) (rename m jm) (rename m outs)

instance Names Formula where
  collect fml = case fml of
    FormLookup lkv ev rv sts ->
      S.unions [collect lkv, collect ev, collect rv, collect sts]
    FormJudgement jmv rbs jm outs ->
      S.unions [collect jmv, collect rbs, collect jm, collect outs]
  rename m fml = case fml of
    FormLookup lkv ev mv sts ->
      FormLookup (rename m lkv) (rename m ev) (rename m mv) (rename m sts)
    FormJudgement jmv rbs jm outs ->
      FormJudgement (rename m jmv) (rename m rbs) (rename m jm) (rename m outs)

instance Names RuleBindSpecItem where
  collect (RuleBsiBinding bv sts) = S.unions [collect bv, collect sts]
  collect (RuleBsiCall _fn jv) = collect jv
  rename m rbsi = case rbsi of
    RuleBsiBinding bv sts -> RuleBsiBinding (rename m bv) (rename m sts)
    RuleBsiCall fn jv -> RuleBsiCall fn (rename m jv)

instance Names Judgement where
  collect (Judgement _ mbSe sts outs)    =
    S.unions [collect mbSe, collect sts, collect outs]
  rename m (Judgement rtn mbSe sts outs) =
    Judgement rtn (rename m mbSe) (rename m sts) (rename m outs)

instance Names SymbolicTerm where
  collect st = case st of
    SymSubtree scp sv                    -> S.unions [collect scp, collect sv]
    SymCtorVarFree scp _ rv              -> S.unions [collect scp, collect rv]
    SymCtorVarBound scp _ bv bbs bsDiff  -> S.unions [collect scp, collect bv, collect bbs, collect bsDiff]
    SymCtorReg scp _ sfs                 -> S.unions [collect scp, collect sfs]
    SymWeaken scp inScp st bv            -> S.unions
                                              [ collect scp, collect inScp
                                              , collect st, collect bv
                                              ]
    SymSubst scp bv st ste               -> S.unions [collect scp, collect bv, collect st, collect ste]
  rename m st = case st of
    SymSubtree scp sv                    -> SymSubtree (rename m scp) (rename m sv)
    SymCtorVarFree scp cn rv             -> SymCtorVarFree (rename m scp) cn (rename m rv)
    SymCtorVarBound scp cn bv bbs bsDiff -> SymCtorVarBound (rename m scp) cn
                                              (rename m bv) (rename m bbs)
                                              (rename m bsDiff)
    SymCtorReg scp cn sfs                -> SymCtorReg (rename m scp) cn (rename m sfs)
    SymWeaken scp inScp st bv            -> SymWeaken (rename m scp) (rename m inScp) (rename m st) (rename m bv)
    SymSubst scp bv st ste               -> SymSubst (rename m scp) (rename m bv) (rename m st) (rename m ste)

instance Names SymbolicCoTerm where
  collect sct
    | SymCoHole _ <- sct
    = S.empty
    | SymCoCtorReg scp bs _ preSfs sct' postSfs <- sct
    = S.unions
        [ collect scp
        , collect bs
        , collect preSfs
        , collect sct'
        , collect postSfs
        ]
  rename m sct
    | SymCoHole stn <- sct
    = SymCoHole stn
    | SymCoCtorReg scp bs cn preSfs sct' postSfs <- sct
    = SymCoCtorReg
        (rename m scp) (rename m bs) cn (rename m preSfs)
        (rename m sct') (rename m postSfs)

instance Names SortVariablePos where
  collect (SortVariablePos jmv rbs jmt pre sct post) =
    S.unions [collect jmv, collect rbs, collect jmt, collect pre, collect sct, collect post]
  rename m (SortVariablePos jmv rbs jmt pre sct post) =
    SortVariablePos (rename m jmv) (rename m rbs) (rename m jmt) (rename m pre) (rename m sct) (rename m post)

instance Names (SymbolicField w) where
  collect sf = case sf of
    SymFieldSort scp bs st       -> S.unions [collect scp, collect bs, collect st]
    SymFieldEnv scp bs se        -> S.unions [collect scp, collect bs, collect se]
    SymFieldBinding bs bv        -> S.unions [collect bs, collect bv]
    SymFieldReferenceFree bs rv  -> S.unions [collect bs, collect rv]
    SymFieldReferenceBound bs bv -> S.unions [collect bs, collect bv]
  rename m sf = case sf of
    SymFieldSort scp bs st       -> SymFieldSort (rename m scp) (rename m bs) (rename m st)
    SymFieldEnv scp bs se        -> SymFieldEnv (rename m scp) (rename m bs) (rename m se)
    SymFieldBinding bs bv        -> SymFieldBinding (rename m bs) (rename m bv)
    SymFieldReferenceFree bs rv  -> SymFieldReferenceFree (rename m bs) (rename m rv)
    SymFieldReferenceBound bs bv -> SymFieldReferenceBound (rename m bs) (rename m bv)

instance Names SymbolicEnv where
  collect se = case se of
    SymEnvVar ev        -> collect ev
    SymEnvNil _         -> S.empty
    SymEnvCons _ se sts -> S.unions [collect se, collect sts]
    SymEnvAppend l r    -> S.unions [collect l, collect r]
  rename m se = case se of
    SymEnvVar ev          -> SymEnvVar (rename m ev)
    SymEnvNil etn         -> SymEnvNil etn
    SymEnvCons ntn se sts -> SymEnvCons ntn (rename m se) (rename m sts)
    SymEnvAppend l r      -> SymEnvAppend (rename m l) (rename m r)

freshen' :: (Names a, FreshM m) => a -> m a
freshen' a = do
  let ns = S.toList $ collect a
  m <- for ns $ \n@(nr,suff) -> do
         suff' <- freshenSuffix nr suff
         return (n,(nr,suff'))
  return (rename (M.fromList m) a)

--------------------------------------------------------------------------------

class Freshen a where
  freshen :: FreshM m => a -> m a
instance Freshen a => Freshen [a] where
  freshen = traverse freshen
instance Freshen FreeVariable where
  freshen (FV nr suff ntn) =
    do
      suff' <- freshenSuffix nr suff
      return $ FV nr suff' ntn
instance Freshen BindingVariable where
  freshen (BV nr suff ntn) =
    do
      suff' <- freshenSuffix nr suff
      return $ BV nr suff' ntn
instance Freshen IndexVar where
  freshen (IndexVar nr suff ntn stn) =
    do
      suff' <- freshenSuffix nr suff
      return $ IndexVar nr suff' ntn stn
instance Freshen SortVariable where
  freshen (SV nr suff stn) =
    do
      suff' <- freshenSuffix nr suff
      return $ SV nr suff' stn
instance Freshen EnvVariable where
  freshen (EV nr suff etn) =
    do
      suff' <- freshenSuffix nr suff
      return $ EV nr suff' etn
instance Freshen JudgementVariable where
  freshen (JV nr suff rtn) =
    do
      suff' <- freshenSuffix nr suff
      return $ JV nr suff' rtn

instance Freshen CtorDecl where
  freshen = freshen'

instance Freshen RelationDecl where
  freshen = freshen'

instance Freshen EnvCtor where
  freshen = freshen'

instance Freshen (FieldDecl w) where
  freshen = freshen'

freshSortVariable :: (EnvM m, FreshM m) => SortTypeName -> m SortVariable
freshSortVariable stn = do
  nrs <- lookupSortRoots stn
  freshen (SV (head nrs) "" stn)

freshBindingVariable :: (EnvM m, FreshM m) => NamespaceTypeName -> m BindingVariable
freshBindingVariable ntn = do
  nrs <- lookupNamespaceRoots ntn
  freshen (BV (head nrs) "" ntn)

freshFreeVariable :: (EnvM m, FreshM m) => NamespaceTypeName -> m FreeVariable
freshFreeVariable ntn = do
  nrs <- lookupNamespaceRoots ntn
  freshen (FV (head nrs) "" ntn)

freshIndexVar :: Elab m => NamespaceTypeName -> m IndexVar
freshIndexVar ntn =
  do
    nrs <- getNamespaceRoots ntn
    (stn,_) <- getNamespaceCtor ntn
    freshen $
      IndexVar (head nrs) "" ntn stn


freshCutoffVar :: FreshM m => NamespaceTypeName -> m CutoffVar
freshCutoffVar ntn = do
  let nr = NR (ntnLoc ntn) "c"
  suff <- freshenSuffix nr ""
  return (CV nr suff ntn)

freshTraceVar :: FreshM m => NamespaceTypeName -> m TraceVar
freshTraceVar ntn = do
  let nr = NR (ntnLoc ntn) "d"
  suff <- freshenSuffix nr ""
  return (TV nr suff ntn)

freshHVarlistVar :: FreshM m => m HVarlistVar
freshHVarlistVar = do
  let nr = NR LocNoWhere "k"
  suff <- freshenSuffix nr ""
  return (HVLV nr suff)

-- freshVarlist :: FreshM m => NamespaceTypeName -> m Varlist
-- freshVarlist ntn =
--   do
--     let nr = NR "k"
--     suff <- freshenSuffix nr ""
--     return (Varlist nr suff ntn)

freshInductionHypothesis :: FreshM m => SortVariable -> m Hypothesis
freshInductionHypothesis (SV (NR loc nr) suff _) = do
  let ihnr = NR loc $ "IH" ++ nr
  suff <- freshenSuffix ihnr suff
  return (Hypothesis ihnr suff)

freshHypothesis :: FreshM m => m Hypothesis
freshHypothesis = Hypothesis (NR LocNoWhere "H") <$> freshenSuffix (NR LocNoWhere "H") ""

freshLookupVar :: FreshM m =>
  SymbolicEnv -> FreeVariable -> [SymbolicField 'WOMV] -> m LookupVar
freshLookupVar se fv sfs = do
  let nr = NR LocNoWhere "lk"
  LookupVar nr
    <$> freshenSuffix nr ""
    <*> pure se
    <*> pure fv
    <*> pure sfs
