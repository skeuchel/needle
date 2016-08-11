{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}

module KnotSpec.NameResolution where


import           Knot.Fresh
import           KnotSpec.Syntax

import           Control.Applicative
import           Control.Monad
import           Control.Monad.Error.Class
import           Control.Monad.Reader.Class
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.Reader (ReaderT, runReaderT, Reader, runReader)
import           Control.Monad.Trans.Writer.Strict (WriterT, execWriterT)
import           Control.Monad.Writer.Class
import           Data.Foldable (for_, traverse_)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Maybe
import           Data.Monoid ((<>))
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Traversable

{-------------------------------------------------------------------------------

In the name resolution phase sort, binding and free variables are resolved to
their declarations sites. Additionally, the variables in function declarations
are renamed to the names used in the constructor declarations of the sort. This
invariant is used in the type checking phase.

-------------------------------------------------------------------------------}

varResolution :: (MonadError String m, FreshM m, EnvM m) => TermSpec 'ResolvedTypes ->
  m (TermSpec 'ResolvedVars)
varResolution (TermSpecRaw decls) = do
  let nds = [ nd | ND nd <- decls ]
      sds = [ sd | SD sd <- decls ]
      eds = [ ed | ED ed <- decls ]
      zds = [ zd | ZD zd <- decls ]
      fds = [ fd | FD fd <- decls ]
      rds = [ rd | RD rd <- decls ]

  nds' <- traverse resolveNamespaceDecl nds
  sds' <- traverse resolveSortDecl sds
  eds' <- traverse resolveEnvDecl eds
  zds' <- traverse resolveSetDecl zds

  let lookupCtorsEnv = mkLookupCtorsEnv sds' zds'
  flip runLookupCtors lookupCtorsEnv $ do
    fds' <- traverse resolveFunDecl fds
    rds' <- traverse resolveRelationDecl rds

    return (TermSpec nds' sds' eds' fds' rds' zds')

--------------------------------------------------------------------------------
-- Step 1: We're resolving nameroots to their corresponding typenames in
-- namespace, sort and environment declarations.
--------------------------------------------------------------------------------

resolveFreeVariable :: EnvM m =>
  RawVariable 'ResolvedTypes -> m FreeVariable
resolveFreeVariable (RawVar nr suf resTn) =
  case resTn of
    ResNTN ntn -> pure (FV nr suf ntn)
    ResSTN _   -> fail "KnotSpec.NameResolution.resolveFreeVariable.ResSTN"
    ResETN _   -> fail "KnotSpec.NameResolution.resolveFreeVariable.ResETN"
    ResZTN _   -> fail "KnotSpec.NameResolution.resolveFreeVariable.ResZTN"
    ResRTN _   -> fail "KnotSpec.NameResolution.resolveFreeVariable.ResRTN"

resolveRawVariable :: EnvM m =>
  RawVariable 'ResolvedTypes -> m ResolvedVariable
resolveRawVariable (RawVar nr suf resTn) = do
  case resTn of
    ResNTN ntn -> pure (ResBV $ BV nr suf ntn)
    ResSTN stn -> pure (ResSV $ SV nr suf stn)
    ResETN etn -> pure (ResEV $ EV nr suf etn)
    ResZTN ztn -> pure (ResZV $ ZV nr suf ztn)
    ResRTN rtn -> pure (ResJV $ JV nr suf rtn)

resolveBindingVariable :: EnvM m =>
  RawVariable 'ResolvedTypes -> m BindingVariable
resolveBindingVariable rawVar = do
  resVar <- resolveRawVariable rawVar
  case resVar of
    ResBV bv -> pure bv
    ResSV sv -> fail $
      "expected a meta variable but found sort variable " <> show sv
    ResEV ev -> fail $
      "expected a meta variable but found environment variable " <>
      show ev
    ResZV zv -> fail $
      "expected a meta variable but found set variable " <>
      show zv
    ResJV jv -> fail $
      "expected a meta variable but found judgement variable " <>
      show jv
    ResFV _ -> error "IMPOSSIBLE: KnotSpec.NameResolution.resolveBindingVariable"

resolveSortVariable :: EnvM m =>
  RawVariable 'ResolvedTypes -> m SortVariable
resolveSortVariable rawVar = do
  resVar <- resolveRawVariable rawVar
  case resVar of
    ResBV bv -> fail $
      "expected a sort variable but found binding variable " <> show bv
    ResSV sv -> pure sv
    ResEV ev -> fail $
      "expected a sort variable but found environment variable " <>
      show ev
    ResZV zv -> fail $
      "expected a sort variable but found set variable " <>
      show zv
    ResJV jv -> fail $
      "expected a sort variable but found judgement variable " <>
      show jv
    ResFV _ -> error "IMPOSSIBLE: KnotSpec.NameResolution.resolveSortVariable"

-- resolveEnvVariable :: RawVariable -> Resolve EnvVariable
-- resolveEnvVariable rawVar = do
--   resVar <- resolveRawVariable rawVar
--   case resVar of
--     ResBV bv -> fail $
--       "expected an env variable but found binding variable " <> show bv
--     ResSV sv -> fail $
--       "expected an env variable but found sort variable " <> show sv
--     ResEV ev -> pure ev
--     ResRV _ -> error "IMPOSSIBLE"

resolveSetVariable :: EnvM m =>
  RawVariable 'ResolvedTypes -> m SetVariable
resolveSetVariable rawVar = do
  resVar <- resolveRawVariable rawVar
  case resVar of
    ResBV bv -> fail $
      "expected a set variable but found binding variable " <> show bv
    ResSV sv -> fail $
      "expected a set variable but found sort variable " <>
      show sv
    ResEV ev -> fail $
      "expected a set variable but found environment variable " <>
      show ev
    ResZV zv -> pure zv
    ResJV jv -> fail $
      "expected a set variable but found judgement variable " <>
      show jv
    ResFV _ -> error "IMPOSSIBLE: KnotSpec.NameResolution.resolveSetVariable"

resolveJudgementVariable :: EnvM m =>
  RawVariable 'ResolvedTypes -> m JudgementVariable
resolveJudgementVariable rawVar = do
  resVar <- resolveRawVariable rawVar
  case resVar of
    ResBV bv -> fail $
      "expected a judgement variable but found binding variable " <> show bv
    ResSV sv -> fail $
      "expected a judgement variable but found sort variable " <> show sv
    ResEV ev -> fail $
      "expected a judgement variable but found environment variable " <>
      show ev
    ResZV zv -> fail $
      "expected a judgement variable but found set variable " <>
      show zv
    ResFV _ -> error "IMPOSSIBLE: KnotSpec.NameResolution.resolveJudgementVariable"
    ResJV jv -> pure jv

--------------------------------------------------------------------------------

type LocalEnv = Map (RawVariable 'ResolvedTypes) ResolvedVariable

type ResolutionVars t =
  forall m. (MonadError String m, EnvM m) =>
  t 'ResolvedTypes -> m (t 'ResolvedVars)

resolveNamespaceDecl :: ResolutionVars NamespaceDecl
resolveNamespaceDecl (NamespaceDecl beg ntn nrs mbStn dirs end) =
  pure (NamespaceDecl beg ntn nrs mbStn dirs end)

resolveSortDecl :: ResolutionVars SortDecl
resolveSortDecl (SortDecl stn nrs cds) =
  SortDecl stn nrs <$> traverse resolveCtorDecl cds

resolveCtorDecl :: ResolutionVars CtorDecl
resolveCtorDecl (CtorVar cn rv) =
  CtorVar cn <$> resolveFreeVariable rv
resolveCtorDecl (CtorReg cn fds) = do
  CtorReg cn <$> resolveFieldDecls SWMV fds

resolveFieldDecls :: (MonadError String m, EnvM m) => SWithMV w ->
  [FieldDecl w 'ResolvedTypes 'ResolvedTypes] ->
  m [FieldDecl w 'ResolvedVars 'ResolvedVars]
resolveFieldDecls w fds = do
  fds'  <- traverse (resolveFieldDeclVar w) fds

  let vars :: LocalEnv
      vars = M.fromList
                [ case fd of
                    FieldDeclSort _ _ sv    -> (toRaw sv, ResSV sv)
                    FieldDeclEnv _ _ ev     -> (toRaw ev, ResEV ev)
                    FieldDeclBinding _ _ bv -> (toRaw bv, ResBV bv)
                    FieldDeclSet _ zv       -> (toRaw zv, ResZV zv)
                    FieldDeclReference _ fv -> (toRaw fv, ResFV fv)
                | fd <- fds'
                ]
  traverse (resolveFieldDeclBindspec vars) fds'

resolveFieldDeclVar :: (MonadError String m, EnvM m) =>
  SWithMV w -> FieldDecl w 'ResolvedTypes 'ResolvedTypes ->
  m (FieldDecl w 'ResolvedTypes 'ResolvedVars)
resolveFieldDeclVar _w (FieldDeclReference loc rawVar) =
  FieldDeclReference loc <$> resolveFreeVariable rawVar
resolveFieldDeclVar w (FieldDeclRaw loc rawBs rawVar) = do
  resVar <- resolveRawVariable rawVar
  case resVar of
    ResBV mv
      | SWOMV <- w ->
        throwError $ "Error " <> show loc <> ": found illegal binding field " <> show mv
      | Nil <- rawBs, SWMV <- w -> pure (FieldDeclBinding loc () mv)
      | otherwise    -> throwError $ "Error " <> show loc <> ": found binding " <> show mv <> " with bindspec"
    ResSV sv -> pure (FieldDeclSort loc rawBs sv)
    ResEV ev -> pure (FieldDeclEnv loc rawBs ev)
    ResZV zv
      | Nil <- rawBs -> pure (FieldDeclSet loc zv)
      | otherwise    -> throwError $ "Error " <> show loc <> ": found set field " <> show zv <> " with bindspec"
    ResFV _  -> error "IMPOSSIBLE: KnotSpec.NameResolution.resolveFieldDeclVar"
    ResJV jv -> fail $ "Found judgement variable " ++ show jv ++ " in field declarations"

resolveFieldDeclBindspec :: (MonadError String m, EnvM m) =>
  LocalEnv -> FieldDecl w 'ResolvedTypes 'ResolvedVars ->
  m (FieldDecl w 'ResolvedVars 'ResolvedVars)
resolveFieldDeclBindspec vars fd = case fd of
  FieldDeclSort loc bs sv    -> FieldDeclSort loc
                                <$> resolveBindSpec vars bs
                                <*> pure sv
  FieldDeclEnv loc bs ev     -> FieldDeclEnv loc
                                <$> resolveBindSpec vars bs
                                <*> pure ev
  FieldDeclBinding loc () bv -> FieldDeclBinding loc
                                <$> pure () <*> pure bv
  FieldDeclReference loc rv  -> FieldDeclReference loc
                                <$> pure rv
  FieldDeclSet loc zv        -> pure (FieldDeclSet loc zv)

resolveBindSpec :: LocalEnv -> ResolutionVars BindSpec
resolveBindSpec vars = traverse (resolveBindSpecItem vars)

resolveBindSpecItem :: LocalEnv -> ResolutionVars BindSpecItem
resolveBindSpecItem vars bsi = case bsi of
  BsiBinding raw->
    case M.lookup raw vars of
      Just (ResBV bv) -> pure (BsiBinding bv)
      Just (ResFV _)  -> fail $ loc ++ ".ResFV"
      Just (ResSV _)  -> fail $ loc ++ ".ResSV"
      Just (ResEV _)  -> fail $ loc ++ ".ResEV"
      Just (ResZV _)  -> fail $ loc ++ ".ResZV"
      Just (ResJV _)  -> fail $ loc ++ ".ResJV"
      Nothing -> fail $ "cannot find field for bindspec singleton " <> toIdent raw
    where loc = "KnotSpec.NameResolution.resolveBindspecitem.BsiBinding"
  BsiCall fn raw -> do
    (stn,_) <- lookupFunctionType fn
    case M.lookup raw vars of
      Just (ResSV sv@(SV _ _ stn')) -> do
        unless
          (stn == stn')
          (fail "KnotSpec.NameResolution.resolveBindSpecItem.BsiCall.ResSV")
        pure (BsiCall fn sv)
      Just (ResBV bv)  -> fail $ unlines [loc ++ ".ResBV:", show vars, show bsi, "Variable: " ++ show bv ]
      Just (ResFV fv)  -> fail $ unlines [loc ++ ".ResFV:", show vars, show bsi, "Variable: " ++ show fv ]
      Just (ResEV ev)  -> fail $ unlines [loc ++ ".ResEV:", show vars, show bsi, "Variable: " ++ show ev ]
      Just (ResZV zv)  -> fail $ unlines [loc ++ ".ResZV:", show vars, show bsi, "Variable: " ++ show zv ]
      Just (ResJV jv)  -> fail $ unlines [loc ++ ".ResJV:", show vars, show bsi, "Variable: " ++ show jv ]
      Nothing         -> fail "KnotSpec.NameResolution.resolveBindspecitem."
    where loc = "KnotSpec.NameResolution.resolveBindspecitem"
resolveEnvDecl :: ResolutionVars EnvDecl
resolveEnvDecl (EnvDecl etn nrs ecds) =
  EnvDecl etn nrs <$> traverse resolveEnvCtorDecl ecds

resolveEnvCtorDecl :: ResolutionVars EnvCtorDecl
resolveEnvCtorDecl (EnvCtorNil cn) =
  pure (EnvCtorNil cn)
resolveEnvCtorDecl (EnvCtorCons cn bv fds mbRtn) = do
  bv' <- resolveBindingVariable bv
  fds'  <- traverse (resolveFieldDeclVar SWOMV) fds

  let vars :: LocalEnv
      vars = M.fromList
                [ case fd of
                    FieldDeclSort _ _ sv    -> (toRaw sv, ResSV sv)
                    FieldDeclEnv _ _ ev     -> (toRaw ev, ResEV ev)
                    FieldDeclSet _ zv       -> (toRaw zv, ResZV zv)
                | fd <- fds'
                ]
  fds'' <- traverse (resolveFieldDeclBindspec vars) fds'
  pure $! EnvCtorCons cn bv' fds'' mbRtn

--------------------------------------------------------------------------------

resolveSetDecl :: ResolutionVars SetDecl
resolveSetDecl (SetDecl ztn nrs cds) =
  SetDecl ztn nrs <$> traverse resolveSetCtorDecl cds

resolveSetCtorDecl :: ResolutionVars SetCtorDecl
resolveSetCtorDecl (SetCtor cn fds) =
  SetCtor cn <$> traverse resolveSetFieldDecl fds

resolveSetFieldDecl :: ResolutionVars SetFieldDecl
resolveSetFieldDecl (SetFieldDecl loc rawVar) =
  SetFieldDecl loc <$> resolveSetVariable rawVar

--------------------------------------------------------------------------------
-- Step 4: Check the well-sortedness of function declarations.
--------------------------------------------------------------------------------

class (MonadError String m, EnvM m, FreshM m) => LookupCtorsM m where
  lookupSortCtorDecl :: SortTypeName -> CtorName -> m (CtorDecl 'ResolvedVars)
  lookupSetCtorDecl :: SetTypeName -> CtorName -> m (SetCtorDecl 'ResolvedVars)

type ResolutionCtors t =
  forall m. LookupCtorsM m => t 'ResolvedTypes -> m (t 'ResolvedVars)

lookupSortCtorVar :: LookupCtorsM m => SortTypeName -> CtorName -> m NamespaceTypeName
lookupSortCtorVar stn cn = do
  cd <- lookupSortCtorDecl stn cn
  case cd of
    CtorVar { ctorDeclReference = fv } -> pure (typeNameOf fv)
    CtorReg {} ->
      fail $ "Expected a variable constructor, but found regular constructor "
             <> toIdent cn

lookupSortCtorReg :: LookupCtorsM m =>
  SortTypeName -> CtorName -> m ([FieldDecl 'WMV 'ResolvedVars 'ResolvedVars])
lookupSortCtorReg stn cn = do
  cd <- lookupSortCtorDecl stn cn
  case cd of
    CtorVar {} ->
      fail $ "Expected a regular constructor, but found variable constructor "
             <> toIdent cn
    CtorReg {} -> pure (ctorDeclFields cd)

resolveFunDecl :: ResolutionCtors FunDecl
resolveFunDecl (FunDecl fn stn ntns cases) = do
  cns <- lookupSortCtors stn

  -- Make sure the sort does not have variables
  for_ cns $ \cn -> do
    cd <- lookupSortCtorDecl stn cn
    case cd of
      CtorVar {} -> fail $
        "Function " <> toIdent fn <>
        " defined over sort with variables"
      _         -> pure ()

  -- Check that the function definition is exhaustive
  unless
    (S.fromList cns ==
     S.fromList (map fcCtor cases))
    (fail $ "Function " <> toIdent fn <> " is not exhaustive ")

  FunDecl fn stn ntns <$> traverse (resolveFunCase stn) cases

toResolvedVariable :: FieldDecl w 'ResolvedVars 'ResolvedVars -> ResolvedVariable
toResolvedVariable fd = case fd of
  FieldDeclSort _ _ sv    -> ResSV sv
  FieldDeclEnv _ _ ev     -> ResEV ev
  FieldDeclBinding _ _ bv -> ResBV bv
  FieldDeclReference _ fv -> ResFV fv
  FieldDeclSet _ zv       -> ResZV zv

resolveFunCase :: SortTypeName -> ResolutionCtors FunCase
resolveFunCase stn (FunCase cn ffs rhs) = do
  fds <- lookupSortCtorReg stn cn
  unless (length ffs == length fds)
    (fail $ "reolveFunCase: Pattern has " <> show (length ffs) <>
            " arguments but constructor " <> show cn <>
            " has " <> show (length fds) <>
            " arguments")

  let vars = zipWith
               (\(FunFieldRaw rawVar) fd -> (rawVar,toResolvedVariable fd))
               ffs fds
  ffs' <-
    sequenceA
    [ case res of
        ResSV sv -> pure (FunFieldSort sv)
        ResEV ev -> pure (FunFieldEnv ev)
        ResBV bv -> pure (FunFieldBinding bv)
        ResZV zv -> pure (FunFieldSet zv)
        ResFV fv -> pure (FunFieldReference fv)
        ResJV _jv -> throwError "KnotSpec.NameResolution.resolveFunCase"
    | res <- map toResolvedVariable fds
    ]

  FunCase cn ffs'
    <$> resolveBindSpec (M.fromList vars) rhs

--------------------------------------------------------------------------------

data LookupCtorsEnv =
  LookupCtorsEnv
  { leSortCtorDecl :: Map (SortTypeName,CtorName) (CtorDecl 'ResolvedVars)
  , leSetCtorDecl  :: Map (SetTypeName,CtorName) (SetCtorDecl 'ResolvedVars)
  }

mkLookupCtorsEnv :: [SortDecl 'ResolvedVars] -> [SetDecl 'ResolvedVars] -> LookupCtorsEnv
mkLookupCtorsEnv sds zds =
  LookupCtorsEnv
  { leSortCtorDecl =
      M.fromList
      [ ((sdTypeName sd,ctorDeclName cd), cd)
      | sd <- sds, cd <- sdCtors sd
      ]
  , leSetCtorDecl =
      M.fromList
      [ ((zdTypeName zd, setCtorName cd), cd)
      | zd <- zds, cd <- zdCtors zd
      ]
  }

newtype LookupCtorsT m a =
  LookupCtorsT { fromLookupCtors :: ReaderT LookupCtorsEnv m a }
  deriving (Applicative, Functor, Monad, MonadError e, MonadTrans, EnvM, FreshM)

runLookupCtors :: LookupCtorsT m a -> LookupCtorsEnv -> m a
runLookupCtors (LookupCtorsT m) = runReaderT m

instance (MonadError String m, EnvM m, FreshM m) => LookupCtorsM (LookupCtorsT m) where
  lookupSortCtorDecl stn cn = LookupCtorsT $ do
    mbCd <- asks (M.lookup (stn,cn) . leSortCtorDecl)
    case mbCd of
      Just x  -> pure x
      Nothing -> fail $ "Could not find constructor " <> toIdent cn
  lookupSetCtorDecl ztn cn = LookupCtorsT $ do
    mbCd <- asks (M.lookup (ztn,cn) . leSetCtorDecl)
    case mbCd of
      Just x  -> pure x
      Nothing -> fail $ "Could not find constructor " <> toIdent cn

--------------------------------------------------------------------------------
-- Step 5: Check the well-sortedness of relation declarations.
--------------------------------------------------------------------------------

resolveRelationDecl :: ResolutionCtors RelationDecl
resolveRelationDecl (RelationDecl mbEtn rtn fds nrs outputs rules) =
  RelationDecl mbEtn rtn
    <$> resolveFieldDecls SWOMV fds
    <*> pure nrs
    <*> pure outputs
    <*> traverse (resolveRule mbEtn) rules

toLocal :: RuleMetavarBinder 'ResolvedVars ->
           (RawVariable 'ResolvedTypes, ResolvedVariable)
toLocal rmb = case rmb of
  RuleMetavarSort    () sv -> (toRaw sv, ResSV sv)
  RuleMetavarBinding () bv -> (toRaw bv, ResBV bv)
  RuleMetavarFree       fv -> (toRaw fv, ResFV fv)
  RuleMetavarSet        zv -> (toRaw zv, ResZV zv)

resolveRule :: Maybe EnvTypeName -> ResolutionCtors Rule
resolveRule mbEtn r = case r of
  RuleVar cn () etn fv sfs jm -> do
    rmbs <- execCollect (collectJudgement jm)
    let lenv :: LocalEnv
        lenv = M.fromList (map toLocal rmbs)

    case M.lookup fv lenv of
      Just (ResFV fv') -> do
        let ntn = typeNameOf fv'
        (ftns,_) <- lookupEnvClause etn ntn
        RuleVar cn rmbs etn fv'
          <$> zipWithM (resolveSymbolicField lenv) ftns sfs
          <*> resolveJudgement lenv jm
      _ -> fail "Expected a free variable"

  RuleReg cn () fms jm outputs -> do
    rmbs <- execCollect (traverse_ collectFormula fms <* collectJudgement jm)

    let jmvs :: Map (RawVariable 'ResolvedTypes) ResolvedVariable
        jmvs = M.fromList
                 [ (rv, ResJV jmv)
                 | FormJudgement
                     (Just rv@(RawVar nr suf _)) _
                     (Judgement rtn _ _) () <- fms
                 , let jmv = JV nr suf rtn
                 ]

        lenv :: LocalEnv
        lenv = M.union jmvs (M.fromList (map toLocal rmbs))

    RuleReg cn rmbs
      <$> traverse (resolveFormula mbEtn lenv) fms
      <*> resolveJudgement lenv jm
      <*> traverse
            (\(fn,rbs) ->
                (,) fn
                <$> resolveRuleBindSpec
                      mbEtn lenv rbs
            )
            outputs

--------------------------------------------------------------------------------
-- Step 5.1: Generalize rules over free meta-variables
--------------------------------------------------------------------------------

class LookupCtorsM m => CollectRuleM m where
  subtree        :: SortTypeName -> RawVariable 'ResolvedTypes -> m ()
  binding        :: NamespaceTypeName -> RawVariable 'ResolvedTypes -> m ()
  reference      :: NamespaceTypeName -> RawVariable 'ResolvedTypes -> m ()
  set            :: SetTypeName -> RawVariable 'ResolvedTypes -> m ()
type CollectRule t = forall m. CollectRuleM m => t 'ResolvedTypes -> m ()

collectFormula :: CollectRule Formula
collectFormula (FormLookup{}) = pure ()
collectFormula (FormJudgement _ _ jm ()) = collectJudgement jm

collectJudgement :: CollectRule Judgement
collectJudgement (Judgement rtn () sfs) = do
  (_, ftns) <- lookupRelationType rtn
  if length ftns == length sfs
    then zipWithM_ collectSymbolicField ftns sfs
    else fail "collectJudgement"

collectSymbolicSortTerm :: SortTypeName -> CollectRule SymbolicTerm
collectSymbolicSortTerm stn (SymVar () sv) = subtree stn sv
collectSymbolicSortTerm stn (SymCtorVarRaw cn mv) = do
  ntn <- lookupSortCtorVar stn cn
  reference ntn mv
collectSymbolicSortTerm stn (SymCtorRegRaw cn sfs) = do
  fds <- lookupSortCtorReg stn cn
  zipWithM_ collectSymbolicField (map typeNameOf fds) sfs
collectSymbolicSortTerm stn (SymWeaken () () st _) =
  collectSymbolicSortTerm stn st
collectSymbolicSortTerm stn (SymSubst () x st ste) = do
  bv <- resolveBindingVariable x
  mbStn <- lookupNamespaceSort (typeNameOf bv)
  stn' <- case mbStn of
            Just stn -> pure stn
            Nothing -> throwError
                         "KnotSpec.NameResolution.collectSymbolicSortTerm.SymSubst"
  collectSymbolicSortTerm stn' st
  collectSymbolicSortTerm stn ste

collectSymbolicSet :: CollectRuleM m =>
  SetTypeName -> SymbolicTerm 'ResolvedTypes -> m ()
collectSymbolicSet ztn st = case st of
  SymVar () zv        -> set ztn zv
  SymCtorVarRaw _cn _fv ->
    throwError $ "Found var constructor form where a term of type "
      <> show ztn <> " was expected"
  SymCtorRegRaw cn sfs -> do
    SetCtor _cn fds <- lookupSetCtorDecl ztn cn
    zipWithM_ collectSymbolicSetField (map typeNameOf fds) sfs
  SymWeaken _ _ _ _ ->
    throwError $ "Found weakening where a term of type "
      <> show ztn <> " was expected"
  SymSubst _ _ _ _ ->
    throwError $ "Found substitution where a term of type "
      <> show ztn <> " was expected"

collectSymbolicSetField :: CollectRuleM m =>
  SetTypeName -> SymbolicField w 'ResolvedTypes -> m ()
collectSymbolicSetField ztn sf = case sf of
  SymFieldRawVar _loc raw -> set ztn raw
  SymFieldRawTerm _loc st -> collectSymbolicSet ztn st

collectSymbolicField :: FieldTypeName w -> CollectRule (SymbolicField w)
collectSymbolicField (FieldSortTypeName stn) sf
  | SymFieldRawVar _loc raw <- sf = subtree stn raw
  | SymFieldRawTerm _loc st <- sf = collectSymbolicSortTerm stn st
collectSymbolicField (FieldEnvTypeName{}) _ =
  error "NOT IMPLEMENTED: KnotSpec.NameResolution.collectSymbolicField"
collectSymbolicField (FieldBindingTypeName ntn) sf
  | SymFieldRawVar _loc raw <- sf = binding ntn raw
  | SymFieldRawTerm _loc _st <- sf =
      throwError "Found raw term where binding was expected"
collectSymbolicField (FieldReferenceTypeName ntn) sf
  | SymFieldRawVar _loc raw <- sf    = reference ntn raw
  | SymFieldRawTerm _loc _ <- sf  =
      throwError "Found raw term where reference was expected"
collectSymbolicField (FieldSetTypeName ztn) sf
  | SymFieldRawVar _loc raw <- sf = set ztn raw
  | SymFieldRawTerm _loc st <- sf  = collectSymbolicSet ztn st

--------------------------------------------------------------------------------

newtype CollectT m a =
  CollectT
  { fromCollectT :: WriterT (Set (RuleMetavarBinder 'ResolvedVars)) m a
  }
  deriving (Functor, Applicative, Monad, MonadError e, EnvM, FreshM, MonadTrans)

instance LookupCtorsM m => LookupCtorsM (CollectT m) where
  lookupSortCtorDecl     = (lift.) . lookupSortCtorDecl
  lookupSetCtorDecl     = (lift.) . lookupSetCtorDecl

instance LookupCtorsM m => CollectRuleM (CollectT m) where
  subtree stn (RawVar nr suf _) =
    CollectT . tell . S.singleton $
      RuleMetavarSort () (SV nr suf stn)
  binding ntn (RawVar nr suf _) =
    CollectT . tell . S.singleton $
      RuleMetavarBinding () (BV nr suf ntn)
  reference ntn (RawVar nr suf _) =
    CollectT . tell . S.singleton $
      RuleMetavarFree (FV nr suf ntn)
  set ztn (RawVar nr suf _) =
    CollectT . tell . S.singleton $
      RuleMetavarSet (ZV nr suf ztn)

execCollect :: EnvM m => CollectT m a -> m [RuleMetavarBinder 'ResolvedVars]
execCollect (CollectT m) = do
  ruleMetavarBindings <- S.toList <$> execWriterT m

  let bindingVariables :: Set BindingVariable
      bindingVariables    =
        S.fromList [ bv | RuleMetavarBinding () bv <- ruleMetavarBindings ]

      -- Filter out all free reference meta-variables that are also bound
      freeFilter :: RuleMetavarBinder 'ResolvedVars -> Bool
      freeFilter (RuleMetavarFree (FV nr suf ntn)) =
        not (S.member (BV nr suf ntn) bindingVariables)
      freeFilter _ = True

  return (filter freeFilter ruleMetavarBindings)

--------------------------------------------------------------------------------
-- Step 5.2
--------------------------------------------------------------------------------

lookupJudgementVariable :: LocalEnv -> RawVariable 'ResolvedTypes -> JudgementVariable
lookupJudgementVariable lenv raw =
  case M.lookup raw lenv of
    Just (ResJV jmv) -> jmv
    _ -> error "KnotSpec.NameResolution.lookupJudgementVariable"

resolveJudgementVariable' :: EnvM m =>
  RelationTypeName -> RawVariable 'ResolvedTypes -> m JudgementVariable
resolveJudgementVariable' rtn (RawVar nr suf _mbRtn) =
  -- TODO: Check that rtn and mbRtn are consistent
  pure (JV nr suf rtn)

resolveFormula :: Maybe EnvTypeName -> LocalEnv -> ResolutionCtors Formula
resolveFormula _mbEtn lenv (FormLookup etn raw sfs) = case M.lookup raw lenv of
  Just (ResFV fv) -> do
    let ntn = typeNameOf fv
    (ftns,_) <- lookupEnvClause etn ntn
    FormLookup etn fv
      <$> zipWithM (resolveSymbolicField lenv) ftns sfs
  _ -> fail "Expected a free variable"
resolveFormula mbEtn lenv (FormJudgement jv rbsis jm@(Judgement rtn _ _) ()) = do
  outs <- lookupRelationOutputs rtn
  FormJudgement
    <$> maybe (freshJudgementVariable rtn) (resolveJudgementVariable' rtn) jv
    <*> resolveRuleBindSpec mbEtn lenv rbsis
    <*> resolveJudgement lenv jm
    <*> traverse (\(fn,etn) -> (,) fn <$> freshEnvVariable etn) outs

resolveJudgement :: LocalEnv -> ResolutionCtors Judgement
resolveJudgement lenv (Judgement rtn () sfs) = do
  (_mbEtn, ftns) <- lookupRelationType rtn
  Judgement rtn () <$>
    zipWithM (resolveSymbolicField lenv) ftns sfs

resolveRuleBindSpec ::
  Maybe EnvTypeName -> LocalEnv -> ResolutionCtors RuleBindSpec
resolveRuleBindSpec mbEtn lenv =
  traverse
    (resolveRuleBindSpecItem
       (fromMaybe (error "") mbEtn) lenv
    )

resolveRuleBindSpecItem :: EnvTypeName -> LocalEnv ->
  ResolutionCtors RuleBindSpecItem
resolveRuleBindSpecItem etn lenv rbsi = case rbsi of
    RuleBsiBinding bv sfs -> do
      bv' <- resolveBindingVariable bv
      (ftns,_) <- lookupEnvClause etn (typeNameOf bv')
      RuleBsiBinding bv'
        <$> zipWithM (resolveSymbolicField lenv) ftns sfs
    RuleBsiCall fn jmv ->
      RuleBsiCall fn <$> pure (lookupJudgementVariable lenv jmv)

resolveSymbolicTerm :: LocalEnv -> SortTypeName -> ResolutionCtors SymbolicTerm
resolveSymbolicTerm lenv stn st = case st of
  SymVar () sv ->
    SymVar () <$> resolveSortVariable sv
  SymCtorVarRaw cn raw ->
    -- ntn <- lookupSortCtorVar stn cn
    case M.lookup raw lenv of
      Just (ResBV bv) -> pure (SymCtorVarBound () cn bv)
      Just (ResFV fv) -> pure (SymCtorVarFree () cn fv)
      _               -> fail "KnotSpec.NameResolution.resolveSymbolicTerm"
  SymCtorRegRaw cn sfs -> do
    fds <- lookupSortCtorReg stn cn
    SymCtorReg () cn
      <$> zipWithM
            (resolveSymbolicField lenv)
            (map typeNameOf fds)
            sfs
  SymWeaken () () st bs ->
    SymWeaken () ()
      <$> resolveSymbolicTerm lenv stn st
      <*> resolveBindSpec lenv bs
  SymSubst () bv st1 st2 -> do
    bv'   <- resolveBindingVariable bv
    mbStn <- lookupNamespaceSort (typeNameOf bv')
    stn'  <- case mbStn of
      Just stn -> pure stn
      Nothing -> throwError
                   "KnotSpec.NameResolution.collectSymbolicSortTerm.SymSubst"
    SymSubst () bv'
      <$> resolveSymbolicTerm lenv stn' st1
      <*> resolveSymbolicTerm lenv stn st2


resolveSymbolicField :: forall w. SWithMVC w =>
  LocalEnv -> FieldTypeName w -> ResolutionCtors (SymbolicField w)
resolveSymbolicField _ _ftn (SymFieldRawVar loc rawVar) = do
  resVar <- resolveRawVariable rawVar
  case resVar of
    ResBV bv -> case sWithMV :: SWithMV w of
                  SWMV -> pure (SymFieldBinding loc () bv)
                  SWOMV -> error ""
    ResSV sv -> pure (SymFieldSort loc () (SymVar () sv))
    ResZV zv -> pure (SymFieldSet loc () (SymSetVar zv))
    ResEV ev -> fail $
      "expected a sort variable or binding variable but found environment " <>
      "variable " <> show ev
    ResJV jv -> fail $ "expected a sort or binding variable but found " <>
      "judgement variable " <> show jv
    ResFV _  -> error "IMPOSSIBLE: KnotSpec.NameResolution.resolveSymbolicField"
resolveSymbolicField lenv ftn (SymFieldRawTerm loc st) =
  let fun = "KnotSpec.NameResolution.resolveSymbolicField.SymFieldRawTerm" in
  case ftn of
    FieldSortTypeName stn ->
      SymFieldSort loc () <$> resolveSymbolicTerm lenv stn st
    FieldSetTypeName ztn ->
      SymFieldSet loc () <$> resolveSymbolicSet lenv ztn st
    FieldEnvTypeName _etn ->
      throwError $ fun ++ ".FieldEnvTypeName: NOT IMPLEMENTED"
    FieldBindingTypeName _ntn ->
      throwError $ fun ++ ".FieldBindingTypeName: IMPOSSIBLE"
    FieldReferenceTypeName _ntn ->
      throwError $ fun ++ ".FieldReferenceTypeName: IMPOSSIBLE"

resolveSymbolicSet :: LookupCtorsM m =>
  LocalEnv -> SetTypeName -> SymbolicTerm 'ResolvedTypes ->
  m (SymbolicSet 'ResolvedVars)
resolveSymbolicSet lenv ztn st = case st of
  SymVar () zv -> do
    zv' <- resolveSetVariable zv
    pure (SymSetVar zv')
  SymCtorVarRaw _cn _fv ->
    throwError $ "Found var constructor form where a term of type "
      <> show ztn <> " was expected"
  SymCtorRegRaw cn sfs -> do
    SetCtor _cn fds <- lookupSetCtorDecl ztn cn
    SymSetCtor cn
      <$> zipWithM
            (resolveSymbolicSetField lenv)
            (map typeNameOf fds)
            sfs
  SymWeaken{} ->
    throwError $ "Found weakening where a term of type "
      <> show ztn <> " was expected"
  SymSubst{} ->
    throwError $ "Found substitution where a term of type "
      <> show ztn <> " was expected"


resolveSymbolicSetField :: LookupCtorsM m =>
  LocalEnv -> SetTypeName ->
  SymbolicField 'WMV 'ResolvedTypes ->
  m (SymbolicSet 'ResolvedVars)
resolveSymbolicSetField lenv ztn sf = case sf of
  SymFieldRawVar _loc rawVar -> do
    resVar <- resolveRawVariable rawVar
    case resVar of
      ResZV zv -> pure (SymSetVar zv)
      _ -> throwError "resolveSymbolicSetField"
  SymFieldRawTerm _loc st -> resolveSymbolicSet lenv ztn st
