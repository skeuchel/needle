{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module KnotCore.Elaboration.Lemma.RelationWellFormed where

import           Coq.StdLib
import           Coq.Syntax

import           KnotCore.DeBruijn.Core
import           KnotCore.Elaboration.Core
import           KnotCore.Elaboration.Eq
import           KnotCore.Syntax

import           Control.Applicative
import           Control.Arrow
import           Control.Monad ((>=>))
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Maybe (catMaybes, mapMaybe)
import           Data.Traversable (for, traverse, sequenceA)

lemmas :: Elab m => [RelationGroupDecl] -> m [Sentence]
lemmas rgds = sequenceA $ mapMaybe eRelationGroupDecl rgds

eRelationGroupDecl :: Elab m => RelationGroupDecl -> Maybe (m Sentence)
eRelationGroupDecl (RelationGroupDecl mbEtn rds)
  | Just _ <- mbEtn
  = Just (SentenceFixpoint . Fixpoint . concat <$> traverse eRelationDecl rds)
  | Nothing <- mbEtn
  = Nothing

eRelationDecl :: Elab m => RelationDecl -> m [FixpointBody]
eRelationDecl (RelationDecl Nothing _ _ _ _ _) =
  error "KnotCore.Elaboration.Lemma.eRelationDecl: impossible"
eRelationDecl (RelationDecl (Just ev) rtn fds _roots _outputs rules) = do
  fds' <- freshen fds
  for (zip fds' [0..]) $
    \(fd,i) -> eRelationDeclI rtn ev fds' fd i rules

eRelationDeclI :: Elab m =>
  RelationTypeName -> EnvVariable ->
  [FieldDecl 'WOMV] -> FieldDecl 'WOMV -> Int -> [Rule] -> m FixpointBody
eRelationDeclI rtn ev fds fd i rules = case fd of
  FieldDeclSort _bs sv _svWf -> do
    jmv <- freshJudgementVariable rtn
    outFnEtns <- lookupRelationOutputs rtn
    outFnEvs <- for outFnEtns $ \(fn,etn) -> (,) fn <$> freshEnvVariable etn
    let jmt =
          Judgement rtn (Just (SymEnvVar ev))
            (map (fieldDeclToSymbolicField Nil) fds)
            (map (second SymEnvVar) outFnEvs)

    binders <-
      sequenceA . concat $
        [ [toBinder ev]
        , eFieldDeclBinders fds
        , map (toBinder.snd) outFnEvs
        , [jvBinder jmv jmt]
        ]

    result <-
      toTerm (WfSort (HVDomainEnv (EVar ev)) (SVar sv))

    equations <- for rules $ \rule ->
      runElabRuleT
        (eRule ev i rule)
        (makeElabRuleEnv (rulePremises rule))
    fs <- eFieldDeclFields fds

    FixpointBody
      <$> idLemmaRelationWellFormed rtn i
      <*> pure binders
      <*> (Just . Struct <$> toId jmv)
      <*> pure result
      <*> (TermMatch
           <$> (MatchItem
                <$> toRef jmv
                <*> pure Nothing
                <*> (Just <$>
                     toTerm
                       (PJudgement rtn
                         JudgementEnvUnderscore
                         fs
                         (map (EVar . snd) outFnEvs)
                       )
                    )
               )
           <*> pure (Just result)
           <*> pure equations
          )

eRule :: ElabRuleM m => EnvVariable -> Int -> Rule -> m Equation
eRule ev i r = case r of
  RuleVar cn rmbs etn fv sfs jm -> do
    lkv   <- freshLookupVar (SymEnvVar ev) fv sfs
    eRule ev i (RuleReg cn rmbs [FormLookup lkv ev fv sfs] jm [])

  RuleReg cn rmbs premises (Judgement _ _ sfs _) _ -> do
    -- Construct the pattern
    wfs   <- catMaybes <$> traverse (eRuleMetavarWellFormed (Just ev)) rmbs

    ids1  <- catMaybes <$> traverse eRuleMetavarId rmbs
    ids2  <- traverse eFormulaId premises
    ids3  <- traverse (toId . snd) wfs
    pat   <- (PatCtorEx
              <$> toQualId cn
              <*> (pure . concat $
                   [ -- The environment parameter is replaced in the match
                     [] -- [PatUnderscore]
                   , map
                       (PatQualId . Ident)
                       (ids1 ++ ids2 ++ ids3)
                   ])
             )

    -- Construct environments for the right hand side
    wfsvs <- M.unions <$> traverse (eRuleMetavarWellFormedSubtree ev) rmbs
    wfivs <- M.unions <$> traverse (eRuleMetavarWellFormedIndex ev) rmbs
    st <- case sfs !! i of
            SymFieldSort _scp _bs st -> pure st
            _ -> error "IMPOSSIBLE"
    rhs <- ewfSymbolicTerm wfsvs wfivs ev st

    return (Equation pat rhs)

--------------------------------------------------------------------------------

eRuleMetavarWellFormedSubtree :: ElabRuleM m =>
  EnvVariable -> RuleMetavarBinder -> m (Map SortVariable Term)
eRuleMetavarWellFormedSubtree ev (RuleMetavarSort bs sv hyp mbPos)
  | Just (SortVariablePos jmv rbs jmt pre sct post) <- mbPos,
    Just se <- jmtEnv jmt
  = do
      fs <- catMaybes <$> traverse symbolicFieldToField (jmtFields jmt)

      call <-
        TermApp
        <$> (idLemmaRelationWellFormed (jmtTypeName jmt) (length pre) >>= toRef)
        <*> (sequenceA . concat $
              [ [symbolicEnvToETerm se >>= toTerm]
              , map toTerm fs
              , map ((>>=toTerm) . symbolicEnvToETerm . snd) (jmtOutputs jmt)
              , [toRef jmv]
              ]
            )
      eqh <-
        eqhSimplify
        <$> (EqhTrans
             <$> (EqhDomainAppend (EVar ev)
                  <$> evalRuleBindSpec (ENil (typeNameOf ev)) rbs)
             <*> (EqhCongAppend (EqhRefl (HVDomainEnv (EVar ev)))
                  <$> eqhvlRuleBindSpecDomain (typeNameOf ev) rbs)
            )

      cast <-
        if isEqhRefl eqh
          then pure call
          else TermApp
               <$> (idLemmaWellFormedTermCast (typeNameOf sv) >>= toRef)
               <*> sequenceA
                   [ pure TermUnderscore
                   , pure TermUnderscore
                   , pure TermUnderscore
                   , pure TermUnderscore
                   , toTerm eqh
                   , toTerm (EqtRefl (typeNameOf sv))
                   , pure call
                   ]
      M.singleton sv <$> eSymbolicCoTerm ev (SymSubtree bs sv) sct cast
  | Nothing <- mbPos
  = M.singleton sv <$> toRef hyp
eRuleMetavarWellFormedSubtree _ _ = pure M.empty

-- TODO: Make pure. Need to make toIndex pure first.
eRuleMetavarWellFormedIndex :: Elab m =>
  EnvVariable -> RuleMetavarBinder ->
  m (Map FreeVariable WellFormedIndexHyp)
eRuleMetavarWellFormedIndex ev (RuleMetavarFree fv hyp) = do
  iv <- toIndex fv
  let hvl   = HVDomainEnv (EVar ev)
      wfiv  = WfIndex hvl (IVar iv)
      wfhyp = WellFormedIndexHyp hyp wfiv
  return $ M.singleton fv wfhyp
eRuleMetavarWellFormedIndex _ _ = pure M.empty

--------------------------------------------------------------------------------

eSymbolicCoTerm :: Elab m => EnvVariable -> SymbolicTerm -> SymbolicCoTerm -> Term -> m Term
eSymbolicCoTerm ev t (SymCoHole _) prf = pure prf
eSymbolicCoTerm ev t (SymCoCtorReg scp bs cn pre sct post) prf = do
  stn <- getCtorSort cn
  TermApp
    <$> (idLemmaWellFormedInversion stn cn (length pre) >>= toRef)
    <*> (sequenceA . concat $
          [ [toTerm (evalScope ev scp)]
          , mapMaybe eSymbolicCoField pre
          , [eSymbolicTerm $ plug t sct]
          , mapMaybe eSymbolicCoField post
          , [eSymbolicCoTerm ev t sct prf]
          ]
        )

eSymbolicCoField :: Elab m => SymbolicField w -> Maybe (m Term)
eSymbolicCoField (SymFieldSort scp bs st)   = pure (eSymbolicTerm st)
eSymbolicCoField (SymFieldBinding scp bv)   = Nothing
eSymbolicCoField (SymFieldReferenceFree{})  =
  error $
    "KnotCore.Elaboration.Lemma.eSymbolicCoField.SymFieldReferenceFree:" ++
    " not implemented"
eSymbolicCoField (SymFieldReferenceBound{}) =
  error $
    "KnotCore.Elaboration.Lemma.eSymbolicCoField.SymFieldReferenceBound:" ++
    " not implemented"

--------------------------------------------------------------------------------

ewfSymbolicTerm :: Elab m =>
  Map SortVariable Term ->
  Map FreeVariable WellFormedIndexHyp ->
  EnvVariable ->
  SymbolicTerm ->
  m Term
ewfSymbolicTerm wfsvs wfivs ev st = case st of
  SymSubtree scp sv -> do
    liftMaybe
      ("RelationWellFormed.ewfSymbolicTerm (" ++
       show wfsvs ++ ") (" ++
       show wfivs ++ ") (" ++
       show ev ++ ") (" ++
       show st ++ ")")
      (M.lookup sv wfsvs)
  SymCtorVarFree scp cn rv -> do
    WellFormedIndexHyp hyp _ <-
      liftMaybe "RelationWellFormed.ewfSymbolicTerm.SymCtorVarFree"
        (M.lookup rv wfivs)
    TermApp
      <$> (idRelationWellFormedCtor cn >>= toRef)
      <*> sequenceA
          [ toTerm (evalScope ev scp)
          , pure TermUnderscore
          , toRef hyp
          ]
  SymCtorVarBound scp cn bv bsBv bsDiff -> do
    stn <- getCtorSort cn
    TermApp
      <$> (idRelationWellFormedCtor cn >>= toRef)
      <*> sequenceA
          [ toTerm (evalScope ev scp)
          , toTerm (IWeaken (I0 (typeNameOf bv) stn) (evalBindSpec HV0 bsDiff))
          , pure (termIdent "I")
          ]
  SymCtorReg scp cn sfs -> do
    wfcn  <- idRelationWellFormedCtor cn >>= toRef
    hvl   <- toTerm (evalScope ev scp)
    wfsfs <- catMaybes <$> traverse (ewfSymbolicField wfsvs wfivs ev) sfs
    return (TermApp wfcn (hvl:wfsfs))
  SymWeaken scp inner st bs -> do

    st' <- symbolicTermToSTerm st
    lem <- idLemmaWeakenWellFormedSort (typeNameOf st')

    TermApp
      <$> toRef lem
      <*> sequenceA
          [ toTerm (evalBindSpec HV0 bs)
          , toTerm (evalScope ev inner)
          , toTerm st'
          , ewfSymbolicTerm wfsvs wfivs ev st
          ]
  SymSubst scp bv s t -> do
    s'    <- symbolicTermToSTerm s
    t'    <- symbolicTermToSTerm t
    lem   <- idLemmaSubstWellFormedSort (typeNameOf bv) (typeNameOf t')
    wf_s  <- ewfSymbolicTerm wfsvs wfivs ev s
    wf_t  <- ewfSymbolicTerm wfsvs wfivs ev t
    hvl'  <- toTerm (HVS (typeNameOf bv) (evalScope ev scp))

    TermApp
      <$> toRef lem
      <*> sequenceA
          [ pure wf_s
          , pure hvl'
          , toTerm t'
          , pure wf_t
          , TermApp
             <$> (idCtorSubstHvlHere (typeNameOf bv) >>= toRef)
             <*> sequenceA [toTerm (evalScope ev scp)]
          ]

ewfSymbolicField :: Elab m =>
  Map SortVariable Term ->
  Map FreeVariable WellFormedIndexHyp ->
  EnvVariable ->
  SymbolicField w ->
  m (Maybe Term)
ewfSymbolicField wfsvs wfivs ev sf = case sf of
  SymFieldSort _ bs st       -> do
    Just <$> ewfSymbolicTerm wfsvs wfivs ev st
  SymFieldBinding _ _          -> pure Nothing
  SymFieldReferenceFree bs rv  ->
    error $ "RelationWellFormed.ewfSymbolicField.SymFieldReferenceFree: " ++
            "NOT IMPLEMENTED"
  SymFieldReferenceBound bs bv ->
    error $ "RelationWellFormed.ewfSymbolicField.SymFieldReferenceBound: " ++
            "NOT IMPLEMENTED"


{-
fix Typing_wf_1 (G : Env) (t : Tm) (T : Ty) (wt : Typing G t T) {struct wt} :
  wfTm (domainEnv G) t :=
  match wt in (Typing _ t0 t1) return (wfTm (domainEnv G) t0) with
  | WtVar _ x _ _ H9 => wfTm_var (domainEnv G) x H9
  | WtAbs T1 T2 t0 wt0 H10 _ =>
      wfTm_abs (domainEnv G) H10 (Typing_wf_1 (evar G T1) t0 T2 wt0)
  | WtApp T11 T12 t1 t2 wt1 wt2 =>
      wfTm_app (domainEnv G) (Typing_wf_1 G t1 (tarrow T11 T12) wt1)
        (Typing_wf_1 G t2 T11 wt2)
  | WtUnit => wfTm_tt (domainEnv G)
  end
with Typing_wf_2 (G : Env) (t : Tm) (T : Ty) (wt : Typing G t T) {struct wt} :
  wfTy (domainEnv G) T :=
  match wt in (Typing _ t0 t1) return (wfTy (domainEnv G) t1) with
  | WtVar _ _ _ H8 _ => H8
  | WtAbs T1 T2 _ _ H10 H11 => wfTy_tarrow (domainEnv G) H10 H11
  | WtApp T11 T12 t1 _ wt1 _ =>
      inversion_wfTy_tarrow_1 (domainEnv G) T11 T12
        (Typing_wf_2 G t1 (tarrow T11 T12) wt1)
  | WtUnit => wfTy_tunit (domainEnv G)
  end
for Typing_wf_1
-}
