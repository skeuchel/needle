{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module KnotCore.Elaboration.Shift.Relation where

import Coq.StdLib
import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core
import KnotCore.Elaboration.Eq

import Control.Applicative
import Control.Arrow
import Control.Monad ((>=>))
import Data.Maybe
import Data.Traversable (for, traverse, sequenceA)

--------------------------------------------------------------------------------

lemmas :: Elab m => [RelationGroupDecl] -> m [Sentence]
lemmas rgds = concat <$> traverse eRelationGroupDecl rgds

eRelationGroupDecl :: Elab m => RelationGroupDecl -> m [Sentence]
eRelationGroupDecl (RelationGroupDecl (Just _etn) rds) = do
  ntns <- getEnvNamespaces
  for ntns $ \ntn -> do
    bodies <- for rds $ \rd -> localNames $ do
      RelationDecl (Just ev) rtn fds _roots _outputs rules <- freshen rd
      eRelationDecl rtn ev fds rules ntn
    pure (SentenceFixpoint (Fixpoint bodies))
eRelationGroupDecl (RelationGroupDecl Nothing _) = pure []

eRelationDecl :: Elab m => RelationTypeName -> EnvVariable -> [FieldDecl 'WOMV] ->
  [Rule] -> NamespaceTypeName -> m FixpointBody
eRelationDecl rtn ev1 fds rules ntn = localNames $ do
  let etn = typeNameOf ev1
  fds' <- freshen fds
  fs' <- eFieldDeclFields fds'

  jmv <- freshJudgementVariable rtn
  outFnEtns <- lookupRelationOutputs rtn
  outFnEvs <- for outFnEtns $ \(fn,etn) -> (,) fn <$> freshEnvVariable etn

  let jmt = Judgement rtn
              (Just (SymEnvVar ev1))
              (map (fieldDeclToSymbolicField Nil) fds')
              (map (second SymEnvVar) outFnEvs)
  cv  <- freshCutoffVar ntn
  ev2 <- freshEnvVariable etn

  insert <-
    InsertEnvHyp
      <$> freshHypothesis
      <*> pure (InsertEnv (CVar cv) (EVar ev1) (EVar ev2))

  result <-
    TermForall
    <$> sequenceA [toBinder cv, toBinder ev2, toBinder insert]
    <*> toTerm
        (PJudgement
           rtn
           (JudgementEnvTerm (EVar ev2))
           (map (shiftField (CVar cv)) fs')
           (map (EShift' (CVar cv) . EVar . snd) outFnEvs)
        )

  equations <- for rules $ \rule ->
     runElabRuleT
       (eRule rtn cv ev1 ev2 insert rule)
       (makeElabRuleEnv (rulePremises rule))

  FixpointBody
    <$> idLemmaShiftRelation etn ntn rtn
    <*> sequenceA
        (toBinder ev1 :
         eFieldDeclBinders fds' ++
         map (toBinder.snd) outFnEvs ++
         [jvBinder jmv jmt]
        )
    <*> pure Nothing
    <*> pure result
    <*> (TermMatch
         <$> (MatchItem
              <$> toRef jmv
              <*> pure Nothing
              <*> (Just <$> toTerm (PJudgement rtn
                                    JudgementEnvUnderscore
                                    fs' (map (EVar . snd) outFnEvs)))
             )
         <*> pure (Just result)
         <*> pure equations
        )

--------------------------------------------------------------------------------

eRule :: ElabRuleM m => RelationTypeName -> CutoffVar -> EnvVariable -> EnvVariable ->
  InsertEnvHyp -> Rule -> m Equation
eRule rtn cv ev1 ev2 ins r = case r of
  RuleVar cn rmbs etn fv sfs jm -> do
    lkv   <- freshLookupVar (SymEnvVar ev1) fv sfs
    wfs   <- catMaybes <$> traverse (eRuleMetavarWellFormed (Just ev1)) rmbs
    ids1  <- catMaybes <$> traverse eRuleMetavarId rmbs
    ids2  <- sequenceA [toId lkv]
    ids3  <- traverse (toId . snd) wfs

    lemma <- idLemmaInsertLookup etn (typeNameOf cv) (typeNameOf fv)
    proof <- TermApp
               <$> toRef lemma
               <*> sequenceA [toRef ins, toRef lkv]
    shiftedFields <- catMaybes <$> traverse (shiftRuleMetavarBinder cv) rmbs
    shiftedWf     <- traverse (uncurry (shiftWellFormedHyp ins)) wfs

    body <-
      TermApp
      <$> toRef cn
      <*> ((:)
           <$> toRef ev2
           <*> pure (shiftedFields ++ [proof] ++ shiftedWf)
          )

    Equation
      <$> (PatCtorEx
           <$> toQualId cn
           <*> (pure . concat $
                [ -- The environment parameter is replaced in the match
                  [] -- [PatUnderscore]
                , map
                    (PatQualId . Ident)
                    (ids1 ++ ids2 ++ ids3)
                ])
          )
      <*> (TermAbs
           <$> sequenceA
               [ toBinder cv
               , toBinder ev2
               , toBinder ins
               ]
           <*> pure body
          )


  RuleReg cn rmbs premises (Judgement _ _ sfs outFnSes) outFnRbs -> do

    wfs   <- catMaybes <$> traverse (eRuleMetavarWellFormed (Just ev1)) rmbs

    ids1  <- catMaybes <$> traverse eRuleMetavarId rmbs
    ids2  <- traverse eFormulaId premises
    ids3  <- traverse (toId . snd) wfs

    proofs        <- traverse (eFormulaProof cv ev2 ins) premises
    shiftedFields <- catMaybes <$> traverse (shiftRuleMetavarBinder cv) rmbs
    shiftedWf     <- traverse (uncurry (shiftWellFormedHyp ins)) wfs


    body <-
      TermApp
      <$> toRef cn
      <*> ((:)
           <$> toRef ev2
           <*> pure (shiftedFields ++ proofs ++ shiftedWf)
          )

    eqts   <- map (eqtSimplify . EqtSym)
                <$> sequenceA (eSymbolicFieldEqs (CVar cv) sfs)
    eqOuts <- for outFnRbs $ \(_fn,rbs) ->
                eqeSimplify . EqeSym
                  <$> eqhvlRuleBindSpecShift (CVar cv) (ENil (typeNameOf ev1)) rbs
    fs <- catMaybes <$> traverse symbolicFieldToField sfs

    eqrefl <- toRef (ID "eq_refl")
    cast <-
      if Prelude.all isEqtRefl eqts && Prelude.all isEqeRefl eqOuts
      then pure body
      else
        TermApp
          <$> (idLemmaRelationCast rtn >>= toRef)
          <*> (sequenceA . concat $
               [ [toRef ev2]
               , -- TODO: The first terms are the ones where the meta-variables
                 -- have been substituted for shifted values. We should eventually
                 -- elaborate into those.
                 map (const (pure TermUnderscore)) fs
               , map (const (pure TermUnderscore)) outFnSes
               , [toRef ev2]
               , map (toTerm . shiftField (CVar cv)) fs
               , map (const (pure TermUnderscore)) outFnSes
                 -- map (symbolicEnvToETerm . snd >=> toTerm) outFnSes -- EShift' ?
               , [pure eqrefl]
               , map toTerm eqts
               , map toTerm eqOuts
               , [pure body]
               ]
              )

    Equation
      <$> (PatCtorEx
           <$> toQualId cn
           <*> (pure . concat $
                [ -- The environment parameter is replaced in the match
                  [] -- [PatUnderscore]
                , map
                    (PatQualId . Ident)
                    (ids1 ++ ids2 ++ ids3)
                ])
          )
      <*> (TermAbs
           <$> sequenceA
               [ toBinder cv
               , toBinder ev2
               , toBinder ins
               ]
           <*> pure cast
          )

--------------------------------------------------------------------------------

shiftRuleMetavarBinder :: ElabRuleM m => CutoffVar -> RuleMetavarBinder -> m (Maybe Term)
shiftRuleMetavarBinder cv (RuleMetavarSort bs sv _ _) =
  Just <$> toTerm (SShift' (CWeaken (CVar cv) (evalBindSpec HV0 bs)) (SVar sv))
shiftRuleMetavarBinder cv (RuleMetavarFree fv _) = do
  iv <- toIndex fv
  Just <$> toTerm (IShift' (CVar cv) (IVar iv))
shiftRuleMetavarBinder _ (RuleMetavarBinding _ _) =
  pure Nothing
shiftRuleMetavarBinder cv (RuleMetavarOutput rbs ev) = do
  delta <- evalRuleBindSpec (ENil (typeNameOf ev)) rbs
  Just <$> toTerm (EShift' (CWeaken (CVar cv) (HVDomainEnv delta)) (EVar ev))

shiftWellFormedHyp :: Elab m => InsertEnvHyp -> BindSpec -> WellFormedHyp -> m Term
shiftWellFormedHyp ins@(InsertEnvHyp _hyp (InsertEnv _c _et1 et2)) bs wf = case wf of
  WellFormedHypSort hyp -> do
    let stn       = typeNameOf hyp
        (ntn,etn) = typeNameOf ins
    call <-
      toTerm $ WellFormedSortShift
        (InsertHvlWeaken (InsertHvlEnv (InsertEnvVar ins)) (evalBindSpec HV0 bs))
        (WellFormedSortVar hyp)

    eqh <-
      eqhSimplify
      <$> (EqhCongAppend (EqhRefl (HVDomainEnv et2))
           <$> (EqhCongAppend (EqhRefl HV0)
                <$> (EqhSym <$> eqhvlEvalBindspecShift ntn bs)
               )
          )

    if isEqhRefl eqh
      then pure call
      else TermApp
           <$> (idLemmaWellFormedTermCast stn >>= toRef)
           <*> sequenceA
               [ pure TermUnderscore
               , pure TermUnderscore
               , pure TermUnderscore
               , pure TermUnderscore
               , toTerm eqh
               , toTerm (EqtRefl stn)
               , pure call
               ]
  WellFormedHypIndex hyp ->
    toTerm $ WellFormedIndexShift
      (InsertHvlWeaken (InsertHvlEnv (InsertEnvVar ins)) (evalBindSpec HV0 bs))
      (WellFormedIndexVar hyp)


eFormulaProof :: ElabRuleM m => CutoffVar -> EnvVariable -> InsertEnvHyp -> Formula -> m Term
eFormulaProof cv _ ins (FormLookup lkv ev mv _)   = do
  lemma <- idLemmaInsertLookup (typeNameOf ev) (typeNameOf cv) (typeNameOf mv)
  TermApp
    <$> toRef lemma
    <*> sequenceA [toRef ins, toRef lkv]
eFormulaProof cv ev2 ins (FormJudgement jmv rbs (Judgement rtn' (Just se1) sfs outFnSes) _fnRbs) = do
  e1  <- symbolicEnvToETerm se1
  let etn = typeNameOf e1

  ex  <- evalRuleBindSpec (ENil etn) rbs
  lem <- idLemmaShiftRelation etn (typeNameOf cv) rtn'

  body <- TermApp
    <$> toRef lem
    <*> (fmap concat . sequenceA $
         [ sequenceA [toTerm e1]
         , traverse symbolicFieldToField sfs
             >>= pure . catMaybes
             >>= traverse toTerm
         , traverse (symbolicEnvToETerm . snd >=> toTerm) outFnSes
         , sequenceA
           [ toRef jmv
           , toTerm . simplifyCutoff $
             CWeaken
             (CVar cv)
             (HVDomainEnv ex)
           , toTerm $ EAppend (EVar ev2) (EShift' (CVar cv) ex) -- TODO: Weaken cv?
           , toTerm $ InsertEnvWeaken (InsertEnvVar ins) ex
           ]
         ]
        )

  eqrefl <- toRef (ID "eq_refl")

  eqe <- eqeSimplify . EqeCongAppend (EqeRefl (EVar ev2))
          <$> eqhvlRuleBindSpecShift (CVar cv) (ENil (typeNameOf ev2)) rbs
  eqh <- eqhvlRuleBindSpecDomain etn rbs
  eqts <-
      map (\eqt ->eqtSimplify $
               EqtTrans
                 (EqtCongShift
                   (EqcCongWeaken (EqcRefl (typeNameOf cv)) eqh)
                   (EqtRefl (typeNameOf eqt))
                 )
                 eqt
          ) <$> sequenceA (eSymbolicFieldEqs (CVar cv) sfs)
  fs <- catMaybes <$> traverse symbolicFieldToField sfs

  if isEqeRefl eqe && Prelude.all isEqtRefl eqts
    then pure body
    else TermApp
         <$> (idLemmaRelationCast rtn' >>= toRef)
         <*> (sequenceA . concat $
              [ [pure TermUnderscore]
              , -- TODO: The first terms are the ones where the meta-variables
                -- have been substituted for shifted values. We should eventually
                -- elaborate into those.
                map (const (pure TermUnderscore)) fs
              , map (const (pure TermUnderscore)) outFnSes
              , [pure TermUnderscore]
              , map (const (pure TermUnderscore)) fs
              , map (const (pure TermUnderscore)) outFnSes
                -- map (symbolicEnvToETerm . snd >=> toTerm) outFnSes -- EShift' ?
              , [toTerm eqe]
              , map toTerm eqts
              , map (const (pure eqrefl)) outFnSes
              , [pure body]
              ]
             )

eFormulaProof _ _ _ (FormJudgement _ _ (Judgement _ Nothing _ _) _) =
  error "NOT IMPLEMENTED: Shift.Relation.eFormula"

--------------------------------------------------------------------------------

eSymbolicTermEq :: Elab m => Cutoff -> SymbolicTerm -> m EqTerm
eSymbolicTermEq _ (SymSubtree _ sv)            = pure (EqtRefl (typeNameOf sv))
eSymbolicTermEq _ (SymCtorVarFree _ cn _)      = EqtRefl <$> getCtorSort cn
eSymbolicTermEq _ (SymCtorVarBound _ cn _ _ _) = EqtRefl <$> getCtorSort cn
eSymbolicTermEq c (SymCtorReg _ cn sfs) =
  EqtCongCtor
    <$> getCtorSort cn
    <*> pure cn
    <*> sequenceA (eSymbolicFieldEqs c sfs)
eSymbolicTermEq c (SymWeaken _ _ st bs)      = do
  st'  <- symbolicTermToSTerm st
  EqtTrans
    <$> pure (EqtSym (EqtCommWeakenShift (evalBindSpec HV0 bs) c st'))
    <*> (EqtCongWeaken
         <$> eSymbolicTermEq c st
         <*> (EqhCongAppend
              <$> pure (EqhRefl HV0)
              <*> (EqhSym <$> eqhvlEvalBindspecShift (typeNameOf c) bs)
             )
        )
eSymbolicTermEq c (SymSubst _ mv st ste)   = do
  ste' <- symbolicTermToSTerm ste
  st'  <- symbolicTermToSTerm st
  deps <- getSortNamespaceDependencies (typeNameOf ste')
  if (typeNameOf c `elem` deps) && (typeNameOf mv `elem` deps)
    then pure (EqtCommShiftSubst0 ste' c (typeNameOf mv) st')
    else pure (EqtRefl (typeNameOf ste'))

eSymbolicFieldEqs :: Elab m => Cutoff -> [SymbolicField w] -> [m EqTerm]
eSymbolicFieldEqs c = mapMaybe (eSymbolicFieldEq c)

eSymbolicFieldEq :: Elab m => Cutoff -> SymbolicField w -> Maybe (m EqTerm)
eSymbolicFieldEq c (SymFieldSort _scp bs st)  =
  Just (eSymbolicTermEq (CWeaken c (evalBindSpec HV0 bs)) st)
eSymbolicFieldEq _c (SymFieldEnv _scp _bs _se)  = error "NOT IMPLEMENTED"
eSymbolicFieldEq _c (SymFieldBinding{}) = Nothing
eSymbolicFieldEq _c (SymFieldReferenceFree{}) = error "NOT IMPLEMENTED"
eSymbolicFieldEq _c (SymFieldReferenceBound{}) = error "NOT IMPLEMENTED"

--------------------------------------------------------------------------------



{-
fix shift_evar_PTyping (G4 : Env) (p23 : Pat) (S4 : Ty)
                       (G5 : Env) (wtp8 : PTyping G4 p23 S4 G5) {struct wtp8} :
  forall (c0 : Cutoff TmVar) (G6 : Env),
  shift_evar c0 G4 G6 -> PTyping G6 (shift_TmVar_Pat c0 p23) S4 G5 :=
  match
    wtp8 in (PTyping _ p24 S5 G6)
    return
      (forall (c0 : Cutoff TmVar) (G7 : Env),
       shift_evar c0 G4 G7 -> PTyping G7 (shift_TmVar_Pat c0 p24) S5 G6)
  with
  | P_Var T34 H30 =>
      fun (c0 : Cutoff TmVar) (G6 : Env) (H35 : shift_evar c0 G4 G6) =>
      PTyping_cast G6 (PVar T34) T34 (evar empty T34) G6
        (PVar T34) T34 (evar empty T34) eq_refl eq_refl eq_refl eq_refl
        (P_Var G6 T34
           (shift_TmVar__wfTy (appendHvl (domainEnv G4) H0) T34 H30
              (weakenCutoffTmVar c0 H0) (appendHvl (domainEnv G6) H0)
              (weaken_shifthvl_TmVar H0 (shift_evar_shifthvl_TmVar H35))))
  | P_Prod T35 T36 p21 p22 G2 G3 wtp6 wtp7 H32 =>
      fun (c0 : Cutoff TmVar) (G6 : Env) (H35 : shift_evar c0 G4 G6) =>
      PTyping_cast G6
        (PProd (shift_TmVar_Pat c0 p21)
           (shift_TmVar_Pat (weakenCutoffTmVar c0 (appendHvl H0 (bind p21)))
              p22)) (TProd T35 T36) (appendEnv (appendEnv empty G2) G3) G6
        (shift_TmVar_Pat c0 (PProd p21 p22)) (TProd T35 T36)
        (appendEnv (appendEnv empty G2) G3) eq_refl eq_refl eq_refl eq_refl
        (P_Prod G6 T35 T36 (shift_TmVar_Pat c0 p21)
           (shift_TmVar_Pat (weakenCutoffTmVar c0 (appendHvl H0 (bind p21)))
              p22) G2 G3
           (PTyping_cast (appendEnv G6 empty)
              (shift_TmVar_Pat (weakenCutoffTmVar c0 (domainEnv empty)) p21)
              T35 G2 (appendEnv G6 empty) (shift_TmVar_Pat c0 p21) T35 G2
              eq_refl eq_refl eq_refl eq_refl
              (shift_evar_PTyping (appendEnv G4 empty) p21 T35 G2 wtp6
                 (weakenCutoffTmVar c0 (domainEnv empty))
                 (appendEnv G6 empty) (weaken_shift_evar empty H35)))
           (PTyping_cast (appendEnv G6 (appendEnv empty G2))
              (shift_TmVar_Pat
                 (weakenCutoffTmVar c0 (domainEnv (appendEnv empty G2))) p22)
              (weakenTy T36 (appendHvl H0 (bind p21))) G3
              (appendEnv G6 (appendEnv empty G2))
              (shift_TmVar_Pat
                 (weakenCutoffTmVar c0 (appendHvl H0 (bind p21))) p22)
              (weakenTy T36 (appendHvl H0 (bind (shift_TmVar_Pat c0 p21))))
              G3 eq_refl
              (f_equal2 shift_TmVar_Pat
                 (f_equal2 weakenCutoffTmVar eq_refl
                    (eq_trans (domainEnv_appendEnv empty G2)
                       (f_equal2 appendHvl eq_refl
                          (domain_PTyping_bind (appendEnv G4 empty) p21 T35
                             G2 wtp6)))) eq_refl)
              (f_equal2 weakenTy eq_refl
                 (f_equal2 appendHvl eq_refl
                    (eq_sym (stability_shift_TmVar__bind p21 c0)))) eq_refl
              (shift_evar_PTyping (appendEnv G4 (appendEnv empty G2)) p22
                 (weakenTy T36 (appendHvl H0 (bind p21))) G3 wtp7
                 (weakenCutoffTmVar c0 (domainEnv (appendEnv empty G2)))
                 (appendEnv G6 (appendEnv empty G2))
                 (weaken_shift_evar (appendEnv empty G2) H35)))
           (shift_TmVar__wfTy (appendHvl (domainEnv G4) H0) T36 H32
              (weakenCutoffTmVar c0 H0) (appendHvl (domainEnv G6) H0)
              (weaken_shifthvl_TmVar H0 (shift_evar_shifthvl_TmVar H35))))
  end
-}

{-
shift_etvar_PTyping =
fix shift_etvar_PTyping (G3 : Env) (p22 : Pat) (S6 : Ty)
                        (G4 : Env) (wtp : PTyping G3 p22 S6 G4) {struct wtp} :
  forall (c1 : Cutoff TyVar) (G5 : Env),
  shift_etvar c1 G3 G5 ->
  PTyping G5 (tshiftPat c1 p22) (tshiftTy c1 S6) (tshiftEnv c1 G4) :=
  match
    wtp in (PTyping _ p23 S7 G5)
    return
      (forall (c1 : Cutoff TyVar) (G6 : Env),
       shift_etvar c1 G3 G6 ->
       PTyping G6 (tshiftPat c1 p23) (tshiftTy c1 S7) (tshiftEnv c1 G5))
  with
  | P_Var T17 H37 =>
      fun (c1 : Cutoff TyVar) (G5 : Env) (H42 : shift_etvar c1 G3 G5) =>
      PTyping_cast G5 (tshiftPat c1 (PVar T17)) (tshiftTy c1 T17)
        (evar empty (tshiftTy c1 T17)) G5 (tshiftPat c1 (PVar T17))
        (tshiftTy c1 T17) (evar empty (tshiftTy c1 T17)) eq_refl eq_refl
        eq_refl eq_refl
        (P_Var G5 (tshiftTy c1 T17)
           (tshift_wfTy (appendHvl (domainEnv G3) H0) T17 H37
              (weakenCutoffTyVar c1 H0) (appendHvl (domainEnv G5) H0)
              (weaken_shifthvl_TyVar H0 (shift_etvar_shifthvl_TyVar H42))))
  | P_Prod T18 T19 p20 p21 G1 G2 wtp5 wtp6 H39 =>
      fun (c1 : Cutoff TyVar) (G5 : Env) (H42 : shift_etvar c1 G3 G5) =>
      PTyping_cast G5 (tshiftPat c1 (PProd p20 p21))
        (tshiftTy c1 (TProd T18 T19))
        (appendEnv
           (appendEnv empty
              (tshiftEnv (weakenCutoffTyVar c1 (domainEnv empty)) G1))
           (tshiftEnv (weakenCutoffTyVar c1 (domainEnv (appendEnv empty G1)))
              G2)) G5 (tshiftPat c1 (PProd p20 p21))
        (tshiftTy c1 (TProd T18 T19))
        (tshiftEnv c1 (appendEnv (appendEnv empty G1) G2)) eq_refl eq_refl
        eq_refl
        (eq_sym
           (eq_trans (tshiftEnv_appendEnv c1 (appendEnv empty G1) G2)
              (f_equal2 appendEnv
                 (eq_trans (tshiftEnv_appendEnv c1 empty G1)
                    (f_equal2 appendEnv eq_refl eq_refl)) eq_refl)))
        (P_Prod G5 (tshiftTy c1 T18) (tshiftTy c1 T19)
           (tshiftPat c1 p20)
           (tshiftPat (weakenCutoffTyVar c1 (appendHvl H0 (bind p20))) p21)
           (tshiftEnv (weakenCutoffTyVar c1 (domainEnv empty)) G1)
           (tshiftEnv (weakenCutoffTyVar c1 (domainEnv (appendEnv empty G1)))
              G2)
           (PTyping_cast (appendEnv G5 (tshiftEnv c1 empty))
              (tshiftPat (weakenCutoffTyVar c1 H0) p20)
              (tshiftTy (weakenCutoffTyVar c1 H0) T18)
              (tshiftEnv (weakenCutoffTyVar c1 (domainEnv empty)) G1)
              (appendEnv G5 (tshiftEnv c1 empty))
              (tshiftPat (weakenCutoffTyVar c1 H0) p20)
              (tshiftTy (weakenCutoffTyVar c1 H0) T18)
              (tshiftEnv (weakenCutoffTyVar c1 (domainEnv empty)) G1) eq_refl
              (f_equal2 tshiftPat
                 (f_equal2 weakenCutoffTyVar eq_refl eq_refl)
                 (eq_sym eq_refl))
              (f_equal2 tshiftTy (f_equal2 weakenCutoffTyVar eq_refl eq_refl)
                 (eq_sym eq_refl)) eq_refl
              (shift_etvar_PTyping (appendEnv G3 empty) p20 T18 G1 wtp5
                 (weakenCutoffTyVar c1 (domainEnv empty))
                 (appendEnv G5 (tshiftEnv c1 empty))
                 (weaken_shift_etvar empty H42)))
           (PTyping_cast (appendEnv G5 (tshiftEnv c1 (appendEnv empty G1)))
              (tshiftPat
                 (weakenCutoffTyVar c1 (domainEnv (appendEnv empty G1))) p21)
              (tshiftTy
                 (weakenCutoffTyVar c1 (domainEnv (appendEnv empty G1)))
                 (weakenTy T19 (appendHvl H0 (bind p20))))
              (tshiftEnv
                 (weakenCutoffTyVar c1 (domainEnv (appendEnv empty G1))) G2)
              (appendEnv G5
                 (appendEnv empty
                    (tshiftEnv (weakenCutoffTyVar c1 (domainEnv empty)) G1)))
              (tshiftPat (weakenCutoffTyVar c1 (appendHvl H0 (bind p20))) p21)
              (weakenTy (tshiftTy c1 T19)
                 (appendHvl H0 (bind (tshiftPat c1 p20))))
              (tshiftEnv
                 (weakenCutoffTyVar c1 (domainEnv (appendEnv empty G1))) G2)
              (f_equal2 appendEnv eq_refl
                 (eq_trans (tshiftEnv_appendEnv c1 empty G1)
                    (f_equal2 appendEnv eq_refl eq_refl)))
              (f_equal2 tshiftPat
                 (f_equal2 weakenCutoffTyVar eq_refl
                    (eq_trans (domainEnv_appendEnv empty G1)
                       (f_equal2 appendHvl eq_refl
                          (domain_PTyping_bind (appendEnv G3 empty) p20 T18
                             G1 wtp5)))) (eq_sym eq_refl))
              (eq_sym
                 (eq_trans
                    (weakenTy_tshiftTy
                       (appendHvl H0 (bind (tshiftPat c1 p20))) c1 T19)
                    (eq_sym
                       (f_equal2 tshiftTy
                          (f_equal2 weakenCutoffTyVar eq_refl
                             (eq_trans (domainEnv_appendEnv empty G1)
                                (f_equal2 appendHvl eq_refl
                                   (eq_trans
                                      (domain_PTyping_bind
                                         (appendEnv G3 empty) p20 T18 G1 wtp5)
                                      (eq_sym (stability_tshift_bind p20 c1))))))
                          (f_equal2 weakenTy eq_refl
                             (f_equal2 appendHvl eq_refl
                                (eq_sym (stability_tshift_bind p20 c1))))))))
              eq_refl
              (shift_etvar_PTyping (appendEnv G3 (appendEnv empty G1)) p21
                 (weakenTy T19 (appendHvl H0 (bind p20))) G2 wtp6
                 (weakenCutoffTyVar c1 (domainEnv (appendEnv empty G1)))
                 (appendEnv G5 (tshiftEnv c1 (appendEnv empty G1)))
                 (weaken_shift_etvar (appendEnv empty G1) H42)))
           (tshift_wfTy (appendHvl (domainEnv G3) H0) T19 H39
              (weakenCutoffTyVar c1 H0) (appendHvl (domainEnv G5) H0)
              (weaken_shifthvl_TyVar H0 (shift_etvar_shifthvl_TyVar H42))))
  end
     : forall (G3 : Env) (p22 : Pat) (S6 : Ty) (G4 : Env),
       PTyping G3 p22 S6 G4 ->
       forall (c1 : Cutoff TyVar) (G5 : Env),
       shift_etvar c1 G3 G5 ->
       PTyping G5 (tshiftPat c1 p22) (tshiftTy c1 S6) (tshiftEnv c1 G4)
-}
