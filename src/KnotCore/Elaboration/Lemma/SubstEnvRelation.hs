{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module KnotCore.Elaboration.Lemma.SubstEnvRelation where

import Coq.StdLib
import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core
import KnotCore.Elaboration.Eq

import Control.Applicative
import Control.Arrow
import Control.Monad ((>=>))
import Data.Maybe
import Data.Traversable
import qualified Data.Set as S

--------------------------------------------------------------------------------

lemmass :: Elab m => [EnvDecl] -> [RelationGroupDecl] -> m [Sentence]
lemmass eds rgds =
  concat <$> sequenceA
    [ lemmas ed rgd
    | ed <- eds
    , rgd <- rgds
    ]

lemmas :: Elab m => EnvDecl -> RelationGroupDecl -> m [Sentence]
lemmas (EnvDecl etn _ ecs) rgd =
  concat <$> sequenceA
  [ do
      subFds'    <- freshen subFds
      eRelationGroupDecl etn subEcn (typeNameOf bv) subFds' mbSubInfo rgd
  | EnvCtorCons subEcn bv subFds mbSubInfo <- ecs
  ]

eRelationGroupDecl :: Elab m =>
  EnvTypeName -> CtorName -> NamespaceTypeName -> [FieldDecl 'WOMV] ->
  Maybe EnvCtorSubst -> RelationGroupDecl -> m [Sentence]
eRelationGroupDecl etn subEcn subNtn subFds mbSubInfo rgd =
  case rgd of
    RelationGroupDecl (Just _etn) rds -> localNames $ do
      bodies <- for rds $ \rd -> localNames $ do
        RelationDecl (Just relEv) relRtn relFds _roots _outputs rules <- freshen rd
        eRelationDecl etn subEcn subNtn subFds mbSubInfo relEv relRtn relFds rules
      pure [SentenceFixpoint (Fixpoint bodies)]
    RelationGroupDecl Nothing _ -> pure []

data EnvCtorSubHyp
  = EnvCtorSubstHypRelation
    { envCtorSubstRelation      ::  RelationTypeName
    , envCtorSubstVarRule       ::  Maybe CtorName
    , envCtorSubstJudgementVar  ::  JudgementVariable
    , envCtorSubstJudgement     ::  Judgement
    }
  | EnvCtorSubstHypWellFormed
    { envCtorSubstWellFormedHyp ::  WellFormedSortHyp
    }
  deriving (Eq,Ord,Show)

instance Ident EnvCtorSubHyp where
  toId hyp = case hyp of
    EnvCtorSubstHypRelation{} -> toId (envCtorSubstJudgementVar hyp)
    EnvCtorSubstHypWellFormed{} -> toId (envCtorSubstWellFormedHyp hyp)
instance KnotCore.Elaboration.Core.Variable EnvCtorSubHyp where
  toBinder hyp = case hyp of
    EnvCtorSubstHypRelation{} ->
      jvBinder (envCtorSubstJudgementVar hyp) (envCtorSubstJudgement hyp)
    EnvCtorSubstHypWellFormed{} ->
      toBinder (envCtorSubstWellFormedHyp hyp)

eRelationDecl :: Elab m =>
  EnvTypeName -> CtorName -> NamespaceTypeName -> [FieldDecl 'WOMV] ->
  Maybe EnvCtorSubst -> EnvVariable -> RelationTypeName -> [FieldDecl 'WOMV] ->
  [Rule] -> m FixpointBody
eRelationDecl etn subEcn subNtn subFds mbSubInfo relEv relRtn relFds rules = localNames $ do
  let en1 = relEv

  ------------------------------------------------------------

  (subStn,subVarCn)  <- getNamespaceCtor subNtn
  en0       <- freshEnvVariable etn
  subFs     <- eFieldDeclFields subFds
  subSv     <- freshSortVariable subStn

  subHyp <- case mbSubInfo of
    Just (EnvCtorSubst subRtn mbVarRule) -> do
      subJmv    <- freshJudgementVariable subRtn
      let subJmt =
            Judgement subRtn (Just (SymEnvVar en0))
              ( SymFieldSort Nil Nil (SymSubtree Nil subSv)
              : map (fieldDeclToSymbolicField Nil) subFds
              ) []

      pure (EnvCtorSubstHypRelation subRtn mbVarRule subJmv subJmt)
    Nothing -> do
      subSvWf <-
        WellFormedSortHyp
        <$> freshHypothesis
        <*> pure (WfSort (HVDomainEnv (EVar en0)) (SVar subSv))
      pure (EnvCtorSubstHypWellFormed subSvWf)

  subBinders <-
        sequenceA $ concat
        [ [ toBinder en0
          , toBinder subSv
          ]
        , eFieldDeclBinders subFds
        , [ toBinder subHyp ]
        ]

  ------------------------------------------------------------

  relFs  <- eFieldDeclFields relFds
  relJmv <- freshJudgementVariable relRtn
  outFnEtns <- lookupRelationOutputs relRtn
  outFnEvs <- for outFnEtns $ \(fn,etn) -> (,) fn <$> freshEnvVariable etn

  let relJmt = Judgement relRtn
              (Just (SymEnvVar en1))
              (map (fieldDeclToSymbolicField Nil) relFds)
              (map (second SymEnvVar) outFnEvs)

  ------------------------------------------------------------

  x         <- freshTraceVar subNtn
  en2       <- freshEnvVariable etn
  substEnv <-
    SubstEnvHyp
      <$> freshHypothesis
      <*> pure (SubstEnv (EVar en0) subFs (SVar subSv) (TVar x)
                        (EVar en1) (EVar en2))

  result <-
    TermForall
    <$> sequenceA [toBinder en2, toBinder x, toBinder substEnv]
    <*> toTerm
        (PJudgement
           relRtn
           (JudgementEnvTerm (EVar en2))
           (map (substField (TVar x) (SVar subSv)) relFs)
           (map (ESubst' (TVar x) (SVar subSv) . EVar . snd) outFnEvs)
        )

  relBinders <-
    sequenceA $ concat
     [ [toBinder en1]
     , eFieldDeclBinders relFds
     , map (toBinder.snd) outFnEvs
     , [jvBinder relJmv relJmt]
     ]

  equations <- for rules $ \rule ->
     runElabRuleT
       (eRule etn subEcn subNtn subFds subSv subHyp relRtn
         en0 x en1 en2 substEnv rule)
       (makeElabRuleEnv (rulePremises rule))

  FixpointBody
    <$> idLemmaSubstRelation etn subNtn relRtn
    <*> pure (subBinders ++ relBinders)
    <*> pure Nothing
    <*> pure result
    <*> (TermMatch
         <$> (MatchItem
              <$> toRef relJmv
              <*> pure Nothing
              <*> (Just <$> toTerm (PJudgement relRtn
                                    JudgementEnvUnderscore
                                    relFs (map (EVar . snd) outFnEvs)))
             )
         <*> pure (Just result)
         <*> pure equations
        )

--------------------------------------------------------------------------------

eRule :: ElabRuleM m =>
  EnvTypeName -> CtorName -> NamespaceTypeName -> [FieldDecl 'WOMV] ->
  SortVariable -> EnvCtorSubHyp ->
  RelationTypeName -> EnvVariable -> TraceVar -> EnvVariable -> EnvVariable ->
  SubstEnvHyp -> Rule -> m Equation
eRule etn subEcn subNtn subFds subSv subHyp relRtn en0 x en1 en2 substEnv r = case r of
  RuleVar cn rmbs etn fv sfs jm
    | typeNameOf fv /= subNtn -> do
        lkv   <- freshLookupVar (SymEnvVar en1) fv sfs
        wfs   <- catMaybes <$> traverse (eRuleMetavarWellFormed (Just en1)) rmbs
        ids1  <- catMaybes <$> traverse eRuleMetavarId rmbs
        ids2  <- sequenceA [toId lkv]
        ids3  <- traverse (toId . snd) wfs

        lemma <- idLemmaSubstEnvLookup etn (typeNameOf x) (typeNameOf fv)
        sfs' <- catMaybes <$> traverse symbolicFieldToField sfs
        lkDeps    <- S.fromList . concat <$>
                     traverse getSortNamespaceDependencies
                       [ typeNameOf st | FieldSort st <- sfs' ]

        proof <- TermApp
                   <$> toRef lemma
                   <*> sequenceA
                       (concat
                        [ eFieldDeclRefs subFds
                        , [ case subHyp of
                              EnvCtorSubstHypRelation _ _ jmv (Judgement rtn (Just se) sfs outFnSes) -> do
                                et <- symbolicEnvToETerm se
                                sfs' <- catMaybes <$> traverse symbolicFieldToField sfs
                                ets <- traverse (symbolicEnvToETerm . snd) outFnSes
                                toTerm (WellFormedSortJudgement 0 (typeNameOf subSv) jmv rtn et sfs' ets)
                              EnvCtorSubstHypWellFormed hyp ->
                                toTerm (WellFormedSortVar hyp)
                          | subNtn `elem` lkDeps
                          ]
                        , [ toRef substEnv
                          ]
                        , map toTerm sfs'
                        , [ toRef lkv ]
                        ]
                       )
        substedFields <- catMaybes <$> traverse (substRuleMetavarBinder x subSv) rmbs
        substedWf     <- traverse (uncurry (substWellFormedHyp subHyp substEnv)) wfs

        body <-
          TermApp
          <$> toRef cn
          <*> ((:)
               <$> toRef en2
               <*> pure (substedFields ++ [proof] ++ substedWf)
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
                   [ toBinder en2
                   , toBinder x
                   , toBinder substEnv
                   ]
               <*> pure body
              )
    | otherwise -> do
        lkv   <- freshLookupVar (SymEnvVar en1) fv sfs
        wfs   <- catMaybes <$> traverse (eRuleMetavarWellFormed (Just en1)) rmbs
        ids1  <- catMaybes <$> traverse eRuleMetavarId rmbs
        ids2  <- sequenceA [toId lkv]
        ids3  <- traverse (toId . snd) wfs

        lemma <- idLemmaSubstEnvLookup etn (typeNameOf x) (typeNameOf fv)
        sfs' <- catMaybes <$> traverse symbolicFieldToField sfs

        body <-
          TermApp
            <$> toRef lemma
            <*> sequenceA
                (concat
                 [ [ toRef en0
                   , toRef subSv
                   ]
                 , eFieldDeclRefs subFds
                 , [ toRef subHyp
                   , toRef x
                   , toRef en1
                   , toRef en2
                   , toRef substEnv
                   , toIndex fv >>= toRef
                   ]
                 , map toTerm sfs'
                 , [ toRef lkv ]
                 ]
                )
          -- refine (subst_evar_lookup_evar G2 s3 T21 jm8 d G1 G3 H34 x9 T22 lk2).

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
                   [ toBinder en2
                   , toBinder x
                   , toBinder substEnv
                   ]
               <*> pure body
              )

  RuleReg cn rmbs premises (Judgement _ _ sfs outFnSes) outFnRbs
    | null [ () | RuleMetavarFree fv _fvWf <- rmbs, typeNameOf fv == subNtn ] -> do

      wfs   <- catMaybes <$> traverse (eRuleMetavarWellFormed (Just en1)) rmbs

      ids1  <- catMaybes <$> traverse eRuleMetavarId rmbs
      ids2  <- traverse eFormulaId premises
      ids3  <- traverse (toId . snd) wfs

      proofs        <- traverse (eFormulaProof en0 x subSv subFds subHyp en2 substEnv) premises
      substedFields <- catMaybes <$> traverse (substRuleMetavarBinder x subSv) rmbs
      substedWf     <- traverse (uncurry (substWellFormedHyp subHyp substEnv)) wfs


      body <-
        TermApp
        <$> toRef cn
        <*> ((:)
             <$> toRef en2
             <*> pure (substedFields ++ proofs ++ substedWf)
            )

      eqts   <- map (eqtSimplify . EqtSym)
                  <$> sequenceA (eSymbolicFieldEqs (TVar x) (SVar subSv) sfs)
      eqOuts <- for outFnRbs $ \(_fn,rbs) ->
                  eqeSimplify . EqeSym
                    <$> eqhvlRuleBindSpecSubst (TVar x) (SVar subSv) (ENil (typeNameOf en1)) rbs
      fs <- catMaybes <$> traverse symbolicFieldToField sfs

      eqrefl <- toRef (ID "eq_refl")
      cast <-
        if Prelude.all isEqtRefl eqts && Prelude.all isEqeRefl eqOuts
        then pure body
        else
          TermApp
            <$> (idLemmaRelationCast relRtn >>= toRef)
            <*> (sequenceA . concat $
                 [ [toRef en2]
                 , -- TODO: The first terms are the ones where the meta-variables
                   -- have been substituted for shifted values. We should eventually
                   -- elaborate into those.
                   map (const (pure TermUnderscore)) fs
                 , map (const (pure TermUnderscore)) outFnSes
                 , [toRef en2]
                 , map (toTerm . substField (TVar x) (SVar subSv)) fs
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
                 [ toBinder en2
                 , toBinder x
                 , toBinder substEnv
                 ]
             <*> pure cast
            )

    | otherwise -> do
      wfs   <- catMaybes <$> traverse (eRuleMetavarWellFormed (Just en1)) rmbs

      ids1  <- catMaybes <$> traverse eRuleMetavarId rmbs
      ids2  <- traverse eFormulaId premises
      ids3  <- traverse (toId . snd) wfs

      proofs        <- traverse (eFormulaProof en0 x subSv subFds subHyp en2 substEnv) premises
      substedFields <- catMaybes <$> traverse (substRuleMetavarBinder x subSv) rmbs
      substedWf     <- traverse (uncurry (substWellFormedHyp subHyp substEnv)) wfs


      body <-
        TermApp
        <$> (idMethodObligationReg etn subNtn cn >>= toRef)
        <*> ((:)
             <$> toRef en2
             <*> pure (substedFields ++ proofs ++ substedWf)
            )

      eqts   <- map (eqtSimplify . EqtSym)
                  <$> sequenceA (eSymbolicFieldEqs (TVar x) (SVar subSv) sfs)
      eqOuts <- for outFnRbs $ \(_fn,rbs) ->
                  eqeSimplify . EqeSym
                    <$> eqhvlRuleBindSpecSubst (TVar x) (SVar subSv) (ENil (typeNameOf en1)) rbs
      fs <- catMaybes <$> traverse symbolicFieldToField sfs

      eqrefl <- toRef (ID "eq_refl")
      cast <-
        if Prelude.all isEqtRefl eqts && Prelude.all isEqeRefl eqOuts
        then pure body
        else
          TermApp
            <$> (idLemmaRelationCast relRtn >>= toRef)
            <*> (sequenceA . concat $
                 [ [toRef en2]
                 , -- TODO: The first terms are the ones where the meta-variables
                   -- have been substituted for shifted values. We should eventually
                   -- elaborate into those.
                   map (const (pure TermUnderscore)) fs
                 , map (const (pure TermUnderscore)) outFnSes
                 , [toRef en2]
                 , map (toTerm . substField (TVar x) (SVar subSv)) fs
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
                 [ toBinder en2
                 , toBinder x
                 , toBinder substEnv
                 ]
             <*> pure cast
            )

--------------------------------------------------------------------------------

substRuleMetavarBinder :: ElabRuleM m => TraceVar -> SortVariable -> RuleMetavarBinder -> m (Maybe Term)
substRuleMetavarBinder xv subSv (RuleMetavarSort bs sv _ _) =
  Just <$> toTerm (SSubst' (TWeaken (TVar xv) (evalBindSpec HV0 bs)) (SVar subSv) (SVar sv))
substRuleMetavarBinder xv subSv (RuleMetavarFree fv _)
  | typeNameOf xv /= typeNameOf fv = do
      iv <- toIndex fv
      Just <$> toTerm (IVar iv)
  | otherwise =
      pure (Just TermUnderscore)
substRuleMetavarBinder _ _ (RuleMetavarBinding _ _) =
  pure Nothing
substRuleMetavarBinder xv subSv (RuleMetavarOutput rbs ev) = do
  delta <- evalRuleBindSpec (ENil (typeNameOf ev)) rbs
  Just <$> toTerm (ESubst' (TWeaken (TVar xv) (HVDomainEnv delta)) (SVar subSv) (EVar ev))

substWellFormedHyp :: Elab m => EnvCtorSubHyp -> SubstEnvHyp -> BindSpec -> WellFormedHyp -> m Term
substWellFormedHyp subHyp subst@(SubstEnvHyp _hyp (SubstEnv et0 subFs subSt _x _et1 et2)) bs wf = case wf of
  WellFormedHypSort hyp -> do
    let stn = typeNameOf hyp
        (subNtn,etn) = typeNameOf subst
    (subStn,subVarCn)  <- getNamespaceCtor subNtn

    wfSubst <-
      WellFormedSortSubst
       <$> (case subHyp of
             EnvCtorSubstHypRelation _ _ jmv (Judgement rtn (Just se) sfs outFnSes) -> do
               et <- symbolicEnvToETerm se
               sfs' <- catMaybes <$> traverse symbolicFieldToField sfs
               ets <- traverse (symbolicEnvToETerm . snd) outFnSes
               pure (WellFormedSortJudgement 0 subStn jmv rtn et sfs' ets)
             EnvCtorSubstHypWellFormed hyp ->
               pure (WellFormedSortVar hyp)
           )
       <*> pure (SubstHvlWeaken (SubstHvlEnv (SubstEnvVar subst)) (evalBindSpec HV0 bs))
       <*> pure (WellFormedSortVar hyp)
    call <-
      toTerm wfSubst

    eqh <-
      eqhSimplify
      <$> (EqhCongAppend (EqhRefl (HVDomainEnv et2))
           <$> (EqhCongAppend (EqhRefl HV0)
                <$> (EqhSym <$> eqhvlEvalBindspecSubst subNtn bs)
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
  WellFormedHypIndex wfi -> do
    let (subNtn,etn) = typeNameOf subst
    (subStn,subVarCn)  <- getNamespaceCtor subNtn
    wfSubst <-
      WellFormedIndexSubst
      <$> (case subHyp of
             EnvCtorSubstHypRelation _ _ jmv (Judgement rtn (Just se) sfs outFnSes) -> do
               et <- symbolicEnvToETerm se
               sfs' <- catMaybes <$> traverse symbolicFieldToField sfs
               ets <- traverse (symbolicEnvToETerm . snd) outFnSes
               pure (WellFormedSortJudgement 0 subStn jmv rtn et sfs' ets)
             EnvCtorSubstHypWellFormed hyp ->
               pure (WellFormedSortVar hyp)
           )
      <*> pure (SubstHvlWeaken (SubstHvlEnv (SubstEnvVar subst)) (evalBindSpec HV0 bs))
      <*> pure (WellFormedIndexVar wfi)
    toTerm wfSubst


eFormulaProof :: ElabRuleM m => EnvVariable -> TraceVar -> SortVariable -> [FieldDecl 'WOMV] -> EnvCtorSubHyp -> EnvVariable -> SubstEnvHyp -> Formula -> m Term
eFormulaProof ev0 xv subSv subFds subHyp _ substEnv (FormLookup lkv ev mv sfs)
  | typeNameOf xv /= typeNameOf mv = do
      lemma <- idLemmaSubstEnvLookup (typeNameOf ev) (typeNameOf xv) (typeNameOf mv)
      sfs' <- catMaybes <$> traverse symbolicFieldToField sfs
      TermApp
        <$> toRef lemma
        <*> sequenceA
            (concat
             [ eFieldDeclRefs subFds
             -- , [ (case subHyp of
             --     EnvCtorSubstHypRelation _ _ jmv (Judgement rtn (Just se) sfs outFnSes) -> do
             --       et <- symbolicEnvToETerm se
             --       sfs' <- catMaybes <$> traverse symbolicFieldToField sfs
             --       ets <- traverse (symbolicEnvToETerm . snd) outFnSes
             --       toTerm (WellFormedSortJudgement 0 (typeNameOf subSv) jmv rtn et sfs' ets)
             --     EnvCtorSubstHypWellFormed hyp ->
             --       toTerm (WellFormedSortVar hyp)
             --     ),
             , [ toRef substEnv ]
             , map toTerm sfs'
             , [ toRef lkv ]
             ]
            )
  | otherwise = do
      lemma <- idLemmaSubstEnvLookup (typeNameOf ev) (typeNameOf xv) (typeNameOf mv)
      sfs' <- catMaybes <$> traverse symbolicFieldToField sfs
      TermApp
        <$> toRef lemma
        <*> sequenceA
            (concat
             [ [ toRef ev0
               , toRef subSv
               ]
             , eFieldDeclRefs subFds
             , [ toRef subHyp
               , toRef xv
               , pure TermUnderscore
               , pure TermUnderscore
               , toRef substEnv
               , toIndex mv >>= toRef
               ]
             , map toTerm sfs'
             , [ toRef lkv ]
             ]
            )
eFormulaProof ev0 xv subSv subFds subHyp ev2 substEnv (FormJudgement jmv rbs (Judgement rtn' (Just se1) sfs outFnSes) _fnRbs) = do
  e1  <- symbolicEnvToETerm se1
  let etn = typeNameOf e1

  ex  <- evalRuleBindSpec (ENil etn) rbs
  lem <- idLemmaSubstRelation etn (typeNameOf xv) rtn'

  body <- TermApp
    <$> toRef lem
    <*> (fmap concat . sequenceA $
         [ sequenceA [toRef ev0, toRef subSv]
         , sequenceA (eFieldDeclRefs subFds)
         , sequenceA [toRef subHyp]
         , sequenceA [toTerm e1]
         , traverse symbolicFieldToField sfs
             >>= pure . catMaybes
             >>= traverse toTerm
         , traverse (symbolicEnvToETerm . snd >=> toTerm) outFnSes
         , sequenceA
           [ toRef jmv
           , toTerm $ EAppend (EVar ev2) (ESubst' (TVar xv) (SVar subSv) ex) -- TODO: Weaken cv?
           , toTerm . simplifyTrace $
             TWeaken
             (TVar xv)
             (HVDomainEnv ex)
           , toTerm $ SubstEnvWeaken (SubstEnvVar substEnv) ex
           ]
         ]
        )

  eqrefl <- toRef (ID "eq_refl")

  eqe <- eqeSimplify . EqeCongAppend (EqeRefl (EVar ev2))
          <$> eqhvlRuleBindSpecSubst (TVar xv) (SVar subSv) (ENil (typeNameOf ev2)) rbs
  eqh <- eqhvlRuleBindSpecDomain etn rbs
  eqts <-
      map (\eqt ->eqtSimplify $
               EqtTrans
                 (EqtCongSubst
                   (EqxCongWeaken (EqxRefl (typeNameOf xv)) eqh)
                   (EqtRefl (typeNameOf subSv))
                   (EqtRefl (typeNameOf eqt))
                 )
                 eqt
          ) <$> sequenceA (eSymbolicFieldEqs (TVar xv) (SVar subSv) sfs)
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

eFormulaProof _ _ _ _ _ _ _ (FormJudgement _ _ (Judgement _ Nothing _ _) _) =
  error "NOT IMPLEMENTED: Shift.Relation.eFormula"

--------------------------------------------------------------------------------

eSymbolicTermEq :: Elab m => Trace -> STerm -> SymbolicTerm -> m EqTerm
eSymbolicTermEq _ _     (SymSubtree _ sv)            = pure (EqtRefl (typeNameOf sv))
eSymbolicTermEq _ _     (SymCtorVarFree _ cn _)      = EqtRefl <$> getCtorSort cn
eSymbolicTermEq _ _     (SymCtorVarBound _ cn _ _ _) = EqtRefl <$> getCtorSort cn
eSymbolicTermEq x subSt (SymCtorReg _ cn sfs) =
  EqtCongCtor
    <$> getCtorSort cn
    <*> pure cn
    <*> sequenceA (eSymbolicFieldEqs x subSt sfs)
eSymbolicTermEq x subSt (SymWeaken _ _ st bs)      = do
  st'  <- symbolicTermToSTerm st
  EqtTrans
    <$> pure (EqtSym (EqtCommWeakenSubst (evalBindSpec HV0 bs) x subSt st'))
    <*> (EqtCongWeaken
         <$> eSymbolicTermEq x subSt st
         <*> (EqhCongAppend
              <$> pure (EqhRefl HV0)
              <*> (EqhSym <$> eqhvlEvalBindspecSubst (typeNameOf x) bs)
             )
        )
eSymbolicTermEq x subSt (SymSubst _ mv st ste)   = do
  ste' <- symbolicTermToSTerm ste
  st'  <- symbolicTermToSTerm st
  deps <- getSortNamespaceDependencies (typeNameOf ste')
  if (typeNameOf x `elem` deps) && (typeNameOf mv `elem` deps)
    then pure (EqtCommSubstSubst0 ste' x subSt (typeNameOf mv) st')
    else pure (EqtRefl (typeNameOf ste'))

eSymbolicFieldEqs :: Elab m => Trace -> STerm -> [SymbolicField w] -> [m EqTerm]
eSymbolicFieldEqs x subSt = mapMaybe (eSymbolicFieldEq x subSt)

eSymbolicFieldEq :: Elab m => Trace -> STerm -> SymbolicField w -> Maybe (m EqTerm)
eSymbolicFieldEq x subSt (SymFieldSort _scp bs st)  =
  Just (eSymbolicTermEq (TWeaken x (evalBindSpec HV0 bs)) subSt st)
eSymbolicFieldEq _x _subSt (SymFieldEnv _scp _bs _se)  = error "NOT IMPLEMENTED"
eSymbolicFieldEq _x _subSt (SymFieldBinding{}) = Nothing
eSymbolicFieldEq _x _subSt (SymFieldReferenceFree{}) = error "NOT IMPLEMENTED"
eSymbolicFieldEq _x _subSt (SymFieldReferenceBound{}) = error "NOT IMPLEMENTED"


{-
fix subst_etvar_Typing (G2 : Env) (S3 : Ty) (H46 : wfTy (domainEnv G2) S3)
                       (G1 : Env) (t : Tm) (T : Ty)
                       (jm12 : Typing G1 t T) {struct jm12} :
  forall (G3 : Env) (d : Trace TyVar),
  subst_etvar G2 S3 d G1 G3 -> Typing G3 (tsubstTm d S3 t) (tsubstTy d S3 T) :=
  match
    jm12 in (Typing _ t0 t1)
    return
      (forall (G3 : Env) (d : Trace TyVar),
       subst_etvar G2 S3 d G1 G3 ->
       Typing G3 (tsubstTm d S3 t0) (tsubstTy d S3 t1))
  with
  | T_Var T0 x lk _ _ =>
      fun (G3 : Env) (d : Trace TyVar) (H47 : subst_etvar G2 S3 d G1 G3) =>
      T_Var G3 (tsubstTy d S3 T0) x (subst_etvar_lookup_evar H46 H47 T0 lk)
        (lookup_evar_wf (tsubstTy d S3 T0)
           (subst_etvar_lookup_evar H46 H47 T0 lk))
        (lookup_evar_wfindex (tsubstTy d S3 T0)
           (subst_etvar_lookup_evar H46 H47 T0 lk))
  | T_Abs T1 T2 t0 jm13 H18 H19 =>
      fun (G3 : Env) (d : Trace TyVar) (H47 : subst_etvar G2 S3 d G1 G3) =>
      T_Abs G3 (tsubstTy d S3 T1) (tsubstTy d S3 T2)
        (tsubstTm (XS TmVar d) S3 t0)
        (Typing_cast (evar G3 (tsubstTy d S3 T1))
           (tsubstTm (XS TmVar d) S3 t0) (tsubstTy (XS TmVar d) S3 T2)
           (evar G3 (tsubstTy d S3 T1)) (tsubstTm (XS TmVar d) S3 t0)
           (tsubstTy d S3 T2) eq_refl eq_refl (tsubstTy_TmVar T2 d S3)
           (subst_etvar_Typing G2 S3 H46 (evar G1 T1) t0 T2 jm13
              (evar G3 (tsubstTy d S3 T1)) (XS TmVar d)
              (subst_etvar_there_evar G2 S3 T1 H47)))
        (substhvl_TyVar_wfTy H46 (domainEnv G1) T1 H18
           (subst_etvar_substhvl_TyVar H47))
        (substhvl_TyVar_wfTy H46 (domainEnv G1) T2 H19
           (subst_etvar_substhvl_TyVar H47))
  | T_App T11 T12 t1 t2 jm12_1 jm12_2 =>
      fun (G3 : Env) (d : Trace TyVar) (H47 : subst_etvar G2 S3 d G1 G3) =>
      T_App G3 (tsubstTy d S3 T11) (tsubstTy d S3 T12)
        (tsubstTm d S3 t1) (tsubstTm d S3 t2)
        (subst_etvar_Typing G2 S3 H46 G1 t1 (tarrow T11 T12) jm12_1 G3 d H47)
        (subst_etvar_Typing G2 S3 H46 G1 t2 T11 jm12_2 G3 d H47)
  | T_Tabs T0 t0 jm13 =>
      fun (G3 : Env) (d : Trace TyVar) (H47 : subst_etvar G2 S3 d G1 G3) =>
      T_Tabs G3 (tsubstTy (XS TyVar d) S3 T0) (tsubstTm (XS TyVar d) S3 t0)
        (subst_etvar_Typing G2 S3 H46 (etvar G1) t0 T0 jm13
           (etvar G3) (XS TyVar d) (subst_etvar_there_etvar G2 S3 H47))
  | T_Tapp T12 T2 t1 jm13 H28 =>
      fun (G3 : Env) (d : Trace TyVar) (H47 : subst_etvar G2 S3 d G1 G3) =>
      Typing_cast G3 (tapp (tsubstTm d S3 t1) (tsubstTy d S3 T2))
        (tsubstTy X0 (tsubstTy d S3 T2)
           (tsubstTy (weakenTrace d (HS TyVar H0)) S3 T12)) G3
        (tapp (tsubstTm d S3 t1) (tsubstTy d S3 T2))
        (tsubstTy d S3 (tsubstTy X0 T2 T12)) eq_refl eq_refl
        (eq_sym (tsubstTy_tsubstTy0_comm T12 d S3 T2))
        (T_Tapp G3 (tsubstTy (weakenTrace d (HS TyVar H0)) S3 T12)
           (tsubstTy d S3 T2) (tsubstTm d S3 t1)
           (subst_etvar_Typing G2 S3 H46 G1 t1 (tall T12) jm13 G3 d H47)
           (substhvl_TyVar_wfTy H46 (domainEnv G1) T2 H28
              (subst_etvar_substhvl_TyVar H47)))
  end



fix subst_etvar_sub (Γ : Env) (B S : Ty) (subS : Sub Γ S B)
                    (Γ1 : Env) (U V : Ty) (sub : Sub Γ1 U V) {struct sub} :
  ∀ (Γ2 : Env) (X : Trace ty),
  subst_etvar Γ B S X Γ1 Γ2 → Sub Γ2 (tsubstTy X S U) (tsubstTy X S V) :=
  match
    sub in (Sub _ t t0)
    return
      (∀ (Γ2 : Env) (X : Trace ty),
       subst_etvar Γ B S X Γ1 Γ2 → Sub Γ2 (tsubstTy X S t) (tsubstTy X S t0))
  with
  | SA_Top S1 H19 =>
      λ (Γ2 : Env) (X : Trace ty) (H : subst_etvar Γ B S X Γ1 Γ2),
      SA_Top Γ2 (tsubstTy X S S1)
        ((λ H0 : wfTy (domainEnv Γ) S,
          (λ _ : wfTy (domainEnv Γ) B,
           substhvl_ty_wfTy H0 (domainEnv Γ1) S1 H19
             (subst_etvar_substhvl_ty B H)) (Sub_wf_1 Γ S B subS))
           (Sub_wf_0 Γ S B subS))
  | SA_Refl_TVar X H20 =>
      λ (Γ2 : Env) (X0 : Trace ty) (H : subst_etvar Γ B S X0 Γ1 Γ2),
      Env_reg_SA_Refl_TVar Γ2 (tsubstIndex X0 S X)
        ((λ H0 : wfTy (domainEnv Γ) S,
          (λ _ : wfTy (domainEnv Γ) B,
           substhvl_ty_wfindex_ty H0 (subst_etvar_substhvl_ty B H) H20)
            (Sub_wf_1 Γ S B subS)) (Sub_wf_0 Γ S B subS))
  | SA_Trans_TVar T U0 X lk sub0 H23 =>
      λ (Γ2 : Env) (X0 : Trace ty) (H : subst_etvar Γ B S X0 Γ1 Γ2),
      Env_reg_SA_Trans_TVar Γ2 (tsubstTy X0 S T) (tsubstTy X0 S U0)
        (tsubstIndex X0 S X)
        (subst_etvar_lookup_etvar Γ S B subS X0 Γ1 Γ2 H X U0 lk)
        (subst_etvar_sub Γ B S subS Γ1 U0 T sub0 Γ2 X0 H)
        ((λ _ : wfTy (domainEnv Γ1) U0,
          (λ _ : wfTy (domainEnv Γ1) T,
           (λ H2 : wfTy (domainEnv Γ) S,
            (λ _ : wfTy (domainEnv Γ) B,
             substhvl_ty_wfindex_ty H2 (subst_etvar_substhvl_ty B H) H23)
              (Sub_wf_1 Γ S B subS)) (Sub_wf_0 Γ S B subS))
            (Sub_wf_1 Γ1 U0 T sub0)) (Sub_wf_0 Γ1 U0 T sub0))
  | SA_Arrow S1 S2 T1 T2 sub1 sub2 =>
      λ (Γ2 : Env) (X : Trace ty) (H : subst_etvar Γ B S X Γ1 Γ2),
      SA_Arrow Γ2 (tsubstTy X S S1) (tsubstTy X S S2)
        (tsubstTy X S T1) (tsubstTy X S T2)
        (subst_etvar_sub Γ B S subS Γ1 T1 S1 sub1 Γ2 X H)
        (subst_etvar_sub Γ B S subS Γ1 S2 T2 sub2 Γ2 X H)
  | SA_All S1 S2 T1 T2 sub1 sub2 =>
      λ (Γ2 : Env) (X : Trace ty) (H : subst_etvar Γ B S X Γ1 Γ2),
      SA_All Γ2 (tsubstTy X S S1) (tsubstTy (XS ty X) S S2)
        (tsubstTy X S T1) (tsubstTy (XS ty X) S T2)
        (subst_etvar_sub Γ B S subS Γ1 T1 S1 sub1 Γ2 X H)
        (subst_etvar_sub Γ B S subS (etvar Γ1 T1) S2 T2 sub2
           (etvar Γ2 (tsubstTy X S T1)) (XS ty X)
           (subst_etvar_there_etvar Γ B S T1 H))
  end
-}
