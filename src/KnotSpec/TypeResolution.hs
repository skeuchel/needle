{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}

module KnotSpec.TypeResolution (typeResolution) where

import           KnotSpec.Syntax

import           Control.Arrow
import           Control.Monad.Error.Class (MonadError, throwError)
import           Control.Monad.Reader.Class (asks)
import           Control.Monad.State.Class (get, modify)
import           Control.Monad.State.Strict (State, runState)
import           Control.Monad.Trans.Reader (ReaderT, runReaderT)
import           Control.Monad.Trans.Writer.Strict (WriterT, runWriterT)
import           Control.Monad.Writer.Class (tell)
import           Data.Foldable (for_)
import           Data.Map (Map)
import qualified Data.Map as M

--------------------------------------------------------------------------------

data Declared
  = DeclaredNTN   NamespaceTypeName
  | DeclaredSTN   SortTypeName
  | DeclaredETN   EnvTypeName
  | DeclaredZTN   SetTypeName
  | DeclaredRTN   RelationTypeName
  | DeclaredNR    NameRoot
  | DeclaredCN    CtorName
  | DeclaredFN    FunName
  deriving (Eq,Ord,Show)

data NameResErr
  = Redeclaration
    { previous      :: Declared
    , redeclaration :: Declared
    }
  | ExpectedNTN
    { expectedNtnLoc   :: Loc
    , expectedNtnFound :: Maybe Declared
    }
  | ExpectedSTN
    { expectedStnLoc   :: Loc
    , expectedStnFound :: Maybe Declared
    }
  | ExpectedETN
    { expectedEtnLoc   :: Loc
    , expectedEtnFound :: Maybe Declared
    }
  | ExpectedZTN
    { expectedZtnLoc   :: Loc
    , expectedZtnFound :: Maybe Declared
    }
  | ExpectedNSETN
    { expectedNsetnLoc   :: Loc
    , expectedNsetnFound :: Maybe Declared
    }
  | ExpectedRTN
    { expectedRtnLoc   :: Loc
    , expectedRtnFound :: Maybe Declared
    }
  | UnknownNR
    { unknownNR         :: NameRoot
    }

instance Show NameResErr where
  show e = case e of
    Redeclaration _ d2  -> "Error: Redeclaration " <> show d2
    ExpectedNTN loc _   -> "Error: Expected namespace type at " <> show loc
    ExpectedSTN loc _   -> "Error: Expected sort type at " <> show loc
    ExpectedETN loc _   -> "Error: Expected environment type at " <> show loc
    ExpectedZTN loc _   -> "Error: Expected set type at " <> show loc
    ExpectedNSETN loc _ -> "Error: Expected term type at " <> show loc
    ExpectedRTN loc _   -> "Error: Expected relation type at " <> show loc
    UnknownNR nr        -> "Error: Can resolve name root " <> nrId nr <>
                            " at " <> show (nrLoc nr)

typeResolution :: (FreshM m, MonadError [NameResErr] m) =>
  TermSpec 'Parsed -> m (TermSpec 'ResolvedTypes)
typeResolution ts =
  case runDeclare (declareTermSpec ts) of
    Left es -> throwError es
    Right table -> runResolveT (resolveTermSpec ts) table

--------------------------------------------------------------------------------
-- Step 1: Perform basic name distinctiveness checks.
--------------------------------------------------------------------------------

class (Applicative m, Monad m) => DeclareM m where
  declareNtn  :: RawTypeName -> [NameRoot] -> m ()
  declareStn  :: RawTypeName -> [NameRoot] -> [CtorName] -> m ()
  declareEtn  :: RawTypeName -> [NameRoot] -> [CtorName] -> m ()
  declareZtn  :: RawTypeName -> [NameRoot] -> [CtorName] -> m ()
  declareRtn  :: RawTypeName -> [NameRoot] -> [CtorName] -> m ()
  declareFn   :: FunName -> m ()

declareTermSpec :: DeclareM m => TermSpec 'Parsed -> m ()
declareTermSpec (TermSpecRaw decls) =
 for_ decls $ \decl -> case decl of
   ND nd -> declareNtn (ndTypeName nd) (ndNameRoots nd)
   SD sd -> declareStn (sdTypeName sd) (sdNameRoots sd)
              (map ctorDeclName $ sdCtors sd)
   FD fd -> declareFn (fdName fd)
   ED ed -> declareEtn (edTypeName ed) (edNameRoots ed)
              (map envCtorName $ edCtors ed)
   ZD zd -> declareZtn (zdTypeName zd) (zdNameRoots zd)
              (map setCtorName $ zdCtors zd)
   RD rd -> declareRtn (rdTypeName rd) (rdNameRoots rd)
              (map ruleName $ rdRules rd)

--------------------------------------------------------------------------------

type SymbolTable = (Map Identifier Declared, Map NameRoot ResolvedTypeName)

newtype Declare a =
  Declare
  { fromDeclare ::
      WriterT
        [NameResErr]
        (State SymbolTable) a
  }
  deriving (Applicative, Functor, Monad)

declare :: Identifier -> Declared -> Declare ()
declare ident d = Declare $ do
  (st,_) <- get
  case M.lookup ident st of
    Nothing -> modify (first $ M.insert ident d)
    Just d' -> tell [Redeclaration d' d]

nameRoot :: NameRoot -> ResolvedTypeName -> Declare ()
nameRoot nr tn = Declare $
  modify (second $ M.insert nr tn)

instance DeclareM Declare where
  declareNtn ntn nrs = do
    let ntn' = rawToNamespaceTypeName ntn
    declare (toIdent ntn) (DeclaredNTN ntn')
    for_ nrs $ flip nameRoot (ResNTN ntn')
    for_ nrs $ \nr -> declare (toIdent nr) (DeclaredNR nr)
  declareStn stn nrs cns = do
    let stn' = rawToSortTypeName stn
    declare (toIdent stn) (DeclaredSTN stn')
    for_ nrs $ flip nameRoot (ResSTN stn')
    for_ nrs $ \nr -> declare (toIdent nr) (DeclaredNR nr)
    for_ cns $ \cn -> declare (toIdent cn) (DeclaredCN cn)
  declareEtn etn nrs cns = do
    let etn' = rawToEnvTypeName etn
    declare (toIdent etn) (DeclaredETN etn')
    for_ nrs $ flip nameRoot (ResETN etn')
    for_ nrs $ \nr -> declare (toIdent nr) (DeclaredNR nr)
    for_ cns $ \cn -> declare (toIdent cn) (DeclaredCN cn)
  declareZtn ztn nrs cns = do
    let ztn' = rawToSetTypeName ztn
    declare (toIdent ztn) (DeclaredZTN ztn')
    for_ nrs $ flip nameRoot (ResZTN ztn')
    for_ nrs $ \nr -> declare (toIdent nr) (DeclaredNR nr)
    for_ cns $ \cn -> declare (toIdent cn) (DeclaredCN cn)
  declareRtn rtn nrs cns = do
    let rtn' = rawToRelationTypeName rtn
    declare (toIdent rtn) (DeclaredRTN rtn')
    for_ nrs $ flip nameRoot (ResRTN rtn')
    for_ cns $ \cn -> declare (toIdent cn) (DeclaredCN cn)
  declareFn fn =
    declare (toIdent fn) (DeclaredFN fn)

runDeclare :: Declare () -> Either [NameResErr] SymbolTable
runDeclare m =
  case runState (runWriterT (fromDeclare m)) (M.empty, M.empty) of
    (((),[]),s)  -> Right s
    ((_,es),_)   -> Left es

--------------------------------------------------------------------------------
-- Step 2: Check the kinds in the definition of functions and relations
--------------------------------------------------------------------------------

class (Applicative m, MonadError [NameResErr] m, FreshM m) => TypeResolveM m where
  resolveIdentifier :: Identifier -> m (Maybe Declared)
  resolveNameRoot   :: NameRoot -> m ResolvedTypeName

resolveNamespaceTypeName :: TypeResolveM m => RawTypeName -> m NamespaceTypeName
resolveNamespaceTypeName tn = do
  d <- resolveIdentifier (toIdent tn)
  case d of
    Just (DeclaredNTN ntn) -> pure ntn
    _                      -> throwError [ExpectedNTN (rawTnLoc tn) d]

resolveSortTypeName :: TypeResolveM m => RawTypeName -> m SortTypeName
resolveSortTypeName tn = do
  d <- resolveIdentifier (toIdent tn)
  case d of
    Just (DeclaredSTN stn) -> pure stn
    _                      -> throwError [ExpectedSTN (rawTnLoc tn) d]

resolveEnvTypeName :: TypeResolveM m => RawTypeName -> m EnvTypeName
resolveEnvTypeName tn = do
  d <- resolveIdentifier (toIdent tn)
  case d of
    Just (DeclaredETN etn) -> pure etn
    _                      -> throwError [ExpectedETN (rawTnLoc tn) d]

-- resolveFieldTypeName :: TypeResolveM m => RawTypeName -> m (FieldTypeName w)
-- resolveFieldTypeName tn = do
--   d <- resolveIdentifier (toIdent tn)
--   case d of
--     Just (DeclaredSTN stn) -> pure (FieldSortTypeName stn)
--     Just (DeclaredZTN ztn) -> pure (FieldSetTypeName ztn)
--     _                      -> throwError [ExpectedSTN (rawTnLoc tn) d]

resolveRelationTypeName :: TypeResolveM m => RawTypeName -> m RelationTypeName
resolveRelationTypeName tn = do
  d <- resolveIdentifier (toIdent tn)
  case d of
    Just (DeclaredRTN ntn) -> pure ntn
    _                      -> throwError [ExpectedRTN (rawTnLoc tn) d]

resolveTypeName ::  TypeResolveM m => RawTypeName -> m ResolvedTypeName
resolveTypeName tn = do
  d <- resolveIdentifier (toIdent tn)
  case d of
    Just (DeclaredNTN ntn) -> pure (ResNTN ntn)
    Just (DeclaredETN etn) -> pure (ResETN etn)
    Just (DeclaredSTN stn) -> pure (ResSTN stn)
    Just (DeclaredRTN rtn) -> pure (ResRTN rtn)
    _                      -> throwError [ExpectedNSETN (rawTnLoc tn) d]

--------------------------------------------------------------------------------

type TypeResolution t =
  forall m. TypeResolveM m => t 'Parsed -> m (t 'ResolvedTypes)

resolveTermSpec :: TypeResolution TermSpec
resolveTermSpec (TermSpecRaw decls) =
  TermSpecRaw <$> traverse resolveDecl decls

resolveDecl :: TypeResolution Decl
resolveDecl (ND nd) = ND <$> resolveNamespaceDecl nd
resolveDecl (SD sd) = SD <$> resolveSortDecl sd
resolveDecl (FD fd) = FD <$> resolveFunDecl fd
resolveDecl (ED ed) = ED <$> resolveEnvDecl ed
resolveDecl (ZD zd) = ZD <$> resolveSetDecl zd
resolveDecl (RD rd) = RD <$> resolveRelationDecl rd

resolveNamespaceDecl :: TypeResolution NamespaceDecl
resolveNamespaceDecl (NamespaceDecl beg ntn nrs mbStn dirs end) =
  NamespaceDecl beg (rawToNamespaceTypeName ntn) nrs
    <$> traverse resolveSortTypeName mbStn
    <*> pure dirs
    <*> pure end

--------------------------------------------------------------------------------

resolveSortDecl :: TypeResolution SortDecl
resolveSortDecl (SortDecl stn nrs cds) =
  SortDecl (rawToSortTypeName stn) nrs
    <$> traverse resolveCtorDecl cds

resolveCtorDecl :: TypeResolution CtorDecl
resolveCtorDecl (CtorVar cn rv)  =
  CtorVar cn <$> resolveRawVariable rv
resolveCtorDecl (CtorReg cn fds) =
  CtorReg cn <$> traverse resolveFieldDecl fds

resolveRawVariable :: TypeResolution RawVariable
resolveRawVariable (RawVarParsed nr suf mbRawTn) = do
  _ <- freshenSuffix nr suf
  resTn <- case mbRawTn of
             Just rawTn -> resolveTypeName rawTn
             Nothing    -> resolveNameRoot nr
  pure $! RawVar nr suf resTn

resolveFieldDecl :: TypeResolveM m =>
  FieldDecl w 'Parsed 'Parsed -> m (FieldDecl w 'ResolvedTypes 'ResolvedTypes)
resolveFieldDecl (FieldDeclRaw loc bs raw)   =
  FieldDeclRaw loc
  <$> resolveBindSpec bs
  <*> resolveRawVariable raw
resolveFieldDecl (FieldDeclReference loc rv) =
  FieldDeclReference loc
  <$> resolveRawVariable rv

resolveBindSpec :: TypeResolution BindSpec
resolveBindSpec = traverse resolveBindSpecItem

resolveBindSpecItem :: TypeResolution BindSpecItem
resolveBindSpecItem (BsiBinding bv) =
  BsiBinding <$> resolveRawVariable bv
resolveBindSpecItem (BsiCall fn sv) =
  BsiCall fn <$> resolveRawVariable sv

--------------------------------------------------------------------------------

resolveFunDecl :: TypeResolution FunDecl
resolveFunDecl (FunDecl fn rawStn rawNtns cases) =
  FunDecl fn
  <$> resolveSortTypeName rawStn
  <*> traverse resolveNamespaceTypeName rawNtns
  <*> traverse resolveFunCase cases

resolveFunCase :: TypeResolution FunCase
resolveFunCase (FunCase cn ffds bs) =
  FunCase cn
  <$> traverse resolveFunField ffds
  <*> resolveBindSpec bs

resolveFunField :: TypeResolution FunField
resolveFunField (FunFieldRaw raw) =
  FunFieldRaw <$> resolveRawVariable raw
resolveFunField (FunFieldReference raw) =
  FunFieldReference <$> resolveRawVariable raw

--------------------------------------------------------------------------------

resolveEnvDecl :: TypeResolution EnvDecl
resolveEnvDecl (EnvDecl etn nrs ecds) =
  EnvDecl (rawToEnvTypeName etn) nrs
    <$> traverse resolveEnvCtorDecl ecds

resolveEnvCtorDecl :: TypeResolution EnvCtorDecl
resolveEnvCtorDecl (EnvCtorNil cn) =
  pure (EnvCtorNil cn)
resolveEnvCtorDecl (EnvCtorCons cn bv efds mbRtn) =
  EnvCtorCons cn
  <$> resolveRawVariable bv
  <*> traverse resolveFieldDecl efds
  <*> traverse resolveRelationTypeName mbRtn

--------------------------------------------------------------------------------

resolveSetDecl :: TypeResolution SetDecl
resolveSetDecl (SetDecl ztn nrs cds) =
  SetDecl (rawToSetTypeName ztn) nrs
    <$> traverse resolveSetCtorDecl cds

resolveSetCtorDecl :: TypeResolution SetCtorDecl
resolveSetCtorDecl (SetCtor cn fds)  =
  SetCtor cn <$> traverse resolveSetFieldDecl fds

resolveSetFieldDecl :: TypeResolution SetFieldDecl
resolveSetFieldDecl (SetFieldDecl loc raw) =
  SetFieldDecl loc <$> resolveRawVariable raw

--------------------------------------------------------------------------------

resolveRelationDecl :: TypeResolution RelationDecl
resolveRelationDecl (RelationDecl mbEtn rawRtn rawFields nrs outputs rules) = do
  mbEtn <- traverse resolveEnvTypeName mbEtn
  RelationDecl mbEtn
    <$> pure (rawToRelationTypeName rawRtn)
    <*> traverse resolveFieldDecl rawFields
    <*> pure nrs
    <*> sequenceA [ (,) fn <$> resolveEnvTypeName rawTn | (fn,rawTn) <- outputs ]
    <*> traverse (resolveRule mbEtn) rules

resolveRule :: Maybe EnvTypeName -> TypeResolution Rule
resolveRule mbEtn r = case r of
  RuleVar cn () () fv sfs conclusion
    | Just etn <- mbEtn ->
        RuleVar cn () etn
        <$> resolveRawVariable fv
        <*> traverse resolveSymbolicField sfs
        <*> resolveJudgement conclusion
    | Nothing <- mbEtn ->
        error "KnotSpec.TypeResolution.resolveRule.RuleVar"
  RuleReg cn () premises conclusion outputs ->
    RuleReg cn ()
    <$> traverse (resolveFormula mbEtn) premises
    <*> resolveJudgement conclusion
    <*> traverse (\(fn,rbs) -> (,) fn <$> resolveRuleBindSpec rbs) outputs

resolveFormula :: Maybe EnvTypeName -> TypeResolution Formula
resolveFormula (Just etn) (FormLookup () rv sfs) =
  FormLookup etn
  <$> resolveRawVariable rv
  <*> traverse resolveSymbolicField sfs
resolveFormula Nothing (FormLookup () rv sfs) =
  error "KnotSpec.TypeResolution.resolveFormula.FormLookup"
resolveFormula _mbEtn (FormJudgement mbJv rbs jm ()) =
  FormJudgement
  <$> traverse resolveRawVariable mbJv
  <*> resolveRuleBindSpec rbs
  <*> resolveJudgement jm
  <*> pure ()

resolveJudgement :: TypeResolution Judgement
resolveJudgement (Judgement rtn () sfs) =
  Judgement
  <$> resolveRelationTypeName rtn
  <*> pure ()
  <*> traverse resolveSymbolicField sfs

resolveRuleBindSpec :: TypeResolution RuleBindSpec
resolveRuleBindSpec = traverse resolveRuleBindSpecItem

resolveRuleBindSpecItem :: TypeResolution RuleBindSpecItem
resolveRuleBindSpecItem rbsi = case rbsi of
  RuleBsiBinding bv sfs ->
    RuleBsiBinding
    <$> resolveRawVariable bv
    <*> traverse resolveSymbolicField sfs
  RuleBsiCall fn jmv ->
    RuleBsiCall fn <$> resolveRawVariable jmv

resolveSymbolicTerm :: TypeResolution SymbolicTerm
resolveSymbolicTerm (SymVar () sv) =
  SymVar ()
  <$> resolveRawVariable sv
resolveSymbolicTerm (SymCtorVarRaw cn mv) =
  SymCtorVarRaw cn
  <$> resolveRawVariable mv
resolveSymbolicTerm (SymCtorRegRaw cn sfs) =
  SymCtorRegRaw cn
  <$> traverse resolveSymbolicField sfs
resolveSymbolicTerm (SymWeaken () () st bs) =
  SymWeaken () ()
  <$> resolveSymbolicTerm st
  <*> resolveBindSpec bs
resolveSymbolicTerm (SymSubst () bv st ste) =
  SymSubst ()
  <$> resolveRawVariable bv
  <*> resolveSymbolicTerm st
  <*> resolveSymbolicTerm ste

resolveSymbolicField :: TypeResolution (SymbolicField w)
resolveSymbolicField (SymFieldRawVar loc raw) =
  SymFieldRawVar loc <$> resolveRawVariable raw
resolveSymbolicField (SymFieldRawTerm loc st) =
  SymFieldRawTerm loc <$> resolveSymbolicTerm st

--------------------------------------------------------------------------------

newtype ResolveT m a =
  ResolveT { fromResolveT :: ReaderT SymbolTable m a }
  deriving (Applicative, Functor, Monad, MonadError e, FreshM, EnvM)

instance (FreshM m, MonadError [NameResErr] m) => TypeResolveM (ResolveT m) where
  resolveIdentifier ident = ResolveT (asks (M.lookup ident . fst))
  resolveNameRoot nr = ResolveT $ do
    mbResTn <- asks (M.lookup nr . snd)
    case mbResTn of
      Just resTn -> pure resTn
      Nothing -> throwError [UnknownNR nr]

runResolveT :: ResolveT m a -> SymbolTable -> m a
runResolveT = runReaderT . fromResolveT
