{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module KnotCore.Elaboration.Lemma.SubstEnvLookup where

import Control.Applicative
import Control.Monad
import Data.Set (Set)
import qualified Data.Set as S


import Coq.StdLib
import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core

lemmass :: Elab m => [EnvDecl] -> m [Sentence]
lemmass = fmap concat . traverse lemmas

lemmas :: Elab m => EnvDecl -> m [Sentence]
lemmas (EnvDecl etn _ ecs) =
  sequenceA
  [ lemma ecs etn (typeNameOf ntn) ecn fds sub
  | EnvCtorCons ecn ntn fds (Just sub) <- ecs
  ]

lemma :: Elab m => [EnvCtor] -> EnvTypeName -> NamespaceTypeName -> CtorName ->
  [FieldDecl 'WOMV] -> EnvCtorSubst -> m Sentence
lemma ecs etn ntn ecn fds (EnvCtorSubst subRtn mbVarRule) = localNames $ do

  (stn,cn)  <- getNamespaceCtor ntn
  en        <- freshEnvVariable etn
  subFds    <- freshen fds
  subFs     <- eFieldDeclFields subFds
  sv        <- freshSortVariable stn
  -- wfs       <- freshVariable "wf" =<<
  --              toTerm (WfSort (HVDomainEnv (EVar en)) (SVar sv))
  jmv       <- freshJudgementVariable subRtn
  let subJmt =
        Judgement subRtn (Just (SymEnvVar en))
          ( SymFieldSort Nil Nil (SymSubtree Nil sv)
          : map (fieldDeclToSymbolicField Nil) subFds
          ) []
  BinderNameType _ subPJmt <- jvBinder jmv subJmt -- HACKY

  x         <- freshTraceVar ntn
  en1       <- freshEnvVariable etn
  en1'      <- freshEnvVariable etn
  en2       <- freshEnvVariable etn
  fv        <- freshFreeVariable ntn
  y         <- toIndex fv
  lkFds     <- freshen fds
  lkFs      <- eFieldDeclFields lkFds
  let substEnvD = SubstEnv (EVar en) subFs (SVar sv) (TVar x)
                        (EVar en1) (EVar en2)
  substEnv  <- freshVariable "sub" =<< toTerm substEnvD
  binders <-
    sequenceA $ concat
    [ [ toBinder en
      , toBinder sv
      ]
    , eFieldDeclBinders subFds
    , [ jvBinder jmv subJmt
      ]
    ]

  statement <-
    TermForall
    <$> sequenceA
        (concat
         [ [ toBinder x
           , toBinder en1
           , toBinder en2
           , toBinder substEnv
           , toBinder y
           ]
         , eFieldDeclBinders lkFds
         ]
        )
    <*> (TermFunction
         <$> toTerm (Lookup (EVar en1) (IVar y) lkFs)
         <*> toTerm
             (PJudgement subRtn (JudgementEnvTerm (EVar en2))
               (FieldSort (SSubstIndex (TVar x) (SVar sv) (IVar y)): map (substField (TVar x) (SVar sv)) lkFs)
               []
             )
        )

  varRule <-
    case mbVarRule of
      Just rcn -> toRef rcn
      Nothing -> idMethodObligationVar etn ntn >>= toRef
  lemma <- idLemmaSubstEnvLookup etn ntn ntn
  return $
    SentenceAssertionProof
      (Assertion AssLemma lemma binders statement)
      (ProofQed [PrTactic "needleGenericSubstEnvLookupHom" [varRule]])

  {-
  lkv <- freshLookupVar
           (SymEnvCons ntn (SymEnvVar en) (map (fieldDeclToSymbolicField Nil) subFds))
           fv
           (map (fieldDeclToSymbolicField Nil) lkFds)
  eqrefl <- toRef (ID "eq_refl")

  eqnHereInnerMatch <-
    TermMatch
    <$> (MatchItem
          <$> toRef en1'
          <*> pure Nothing
          <*> pure Nothing
        )
    <*> pure (Just (TermSort Prop))
    <*> sequenceA
        [ Equation
          <$> (PatCtor
                <$> toQualId ecn
                <*> sequenceA
                ( toId en
                  : eFieldDeclIdentifiers subFds
                )
              )
          <*> (foldr1 TermFunction <$> sequence
                [ pure subPJmt
                , toTerm substEnvD
                , toTerm
                  (PJudgement
                     rtn (JudgementEnvTerm (EVar en))
                     (FieldSort (SSubstIndex (T0 ntn) (SVar sv) (IVar y))
                     : map (substField (T0 ntn) (SVar sv)) lkFs
                     )
                     []
                  )
                ]
              )
        , Equation
          <$> pure PatUnderscore
          <*> pure true
        ]
  eqnHereHere <-
    Equation
    <$> (PatCtor
          <$> (idCtorLookupHere ecn >>= toQualId)
          <*> sequenceA
              ( toId en
                : eFieldDeclIdentifiers subFds
                ++ [pure (ID "_")]
              )
        )
    <*> (TermAbs
          <$> sequenceA
          [ jvBinder jmv subJmt
          , toBinder substEnv
          ]
          <*> toRef jmv
        )
  eqnHereThereHom <-
    Equation
    <$> (PatCtor
          <$> (idCtorLookupThere ecn ecn >>= toQualId)
          <*> sequenceA
              (concat
               [ [ toId en
                 , toId y
                 ]
               , eFieldDeclIdentifiers lkFds
               , eFieldDeclIdentifiers subFds
               , [toId lkv]
               ]
              )
        )
    <*> (TermAbs
         <$> sequenceA
             [ jvBinder jmv subJmt
             , toBinder substEnv
             ]
         <*> (TermApp
              <$> (idLemmaRelationCast rtn >>= toRef)
              <*> (sequenceA . concat $
                   [ [ toRef en
                     , toTerm (SCtorVar stn cn (IVar y))
                     ]
                   , eFieldDeclRefs lkFds
                   , [ toRef en
                     , toTerm (SCtorVar stn cn (IVar y))
                     ]
                   , map (toTerm . substField (T0 ntn) (SVar sv)) lkFs
                   , [ pure eqrefl
                     , pure eqrefl
                     ]
                   , map (const (pure TermUnderscore)) lkFs
                   , [case mbVarRule of
                       Just rcn ->
                         TermApp
                         <$> toRef rcn
                         <*> sequenceA
                             ( toRef en
                             : toRef y
                             : eFieldDeclRefs lkFds
                             )
                       Nothing ->
                         TermApp
                         <$> (idMethodObligationVar etn ntn >>= toRef)
                         <*> sequenceA
                             ( pure TermUnderscore
                             : pure TermUnderscore
                             : map (const (pure TermUnderscore)) lkFds
                             ++ [ toRef lkv
                                , TermApp
                                  <$> (idLemmaLookupWellformedData ecn >>= toRef)
                                  <*>
                                ]
                             )
                     ]
                   ]
                  )
             )
        )

  eqnHere <-
    Equation
     <$> (PatCtor
          <$> (idCtorSubstEnvHere ecn >>= toQualId)
          <*> pure []
         )
     <*> (TermAbs
          <$> sequenceA
              (concat
               [ [toBinder y]
               , eFieldDeclBinders lkFds
               , [toBinder lkv]
               ]
              )
          <*> (TermApp
               <$> (TermMatch
                    <$> (MatchItem
                         <$> toRef lkv
                         <*> pure Nothing
                         <*> (Just <$> toTerm (Lookup (EVar en1') (IVar y) lkFs))
                        )
                    <*> pure (Just eqnHereInnerMatch)
                    <*> sequenceA
                        [ pure eqnHereHere
                        , pure eqnHereThereHom
                        , Equation
                          <$> pure PatUnderscore
                          <*> pure TermUnderscore
                        ]
                   )
                <*> sequenceA
                    [ toRef jmv
                    , toRef substEnv
                    ]
              )
         )

     {-
      | lookup_etvar_there_etvar G0 X19 T46 T47 lk' =>
          fun (_ : Sub G0 S T47) (_ : subst_etvar G0 T47 S X G1 G2) =>
          Sub_cast G0 (tvar X19) T46 G0 (tvar X19)
            (tsubstTy X0 S (tshiftTy C0 T46)) eq_refl eq_refl
            (eq_sym (tsubstTy0_tshiftTy0_reflection T46 S))
            (Sub_var G0 X19 T46 lk')
     -}


  eqnTheres <-
    sequenceA
    [ do
        tfds <- freshen fds'
        Equation
          <$> (PatCtor
               <$> (idCtorSubstEnvThere ecn ecn' >>= toQualId)
               <*> sequenceA
                   ( toId x
                   : toId en1
                   : toId en2
                   : eFieldDeclIdentifiers tfds
                   ++ [toId substEnv]
                   )
              )
          <*> pure TermUnderscore

    | EnvCtorCons ecn' ntn' fds' _ <- ecs
    ]

  match <-
    TermMatch
    <$> (MatchItem
          <$> toRef substEnv
          <*> pure Nothing
          <*> (Just <$> toMatchItem substEnvD)
        )
    <*> pure (Just result)
    <*> pure (eqnHere:eqnTheres)

  body <-
    FixpointBody
    <$> idLemmaSubstEnvLookup etn ntn ntn
    <*> (sequenceA $ concat
          [ [ toBinder en
            , toBinder sv
            ]
          , eFieldDeclBinders subFds
          , [ jvBinder jmv subJmt
            , toBinder x
            , toBinder en1
            , toBinder en2
            , toBinder substEnv
            ]
          ]
        )
    <*> pure Nothing
    <*> pure result
    <*> pure match

  return (SentenceFixpoint (Fixpoint [body]))


{-
 class SubObligations : Prop :=
   { Sub_var :
       forall G X T, lookup_etvar G X T -> Sub G (tvar X) T;
   }

subst_etvar_lookup_etvar =
fix subst_etvar_lookup_etvar (G : Env) (B S : Ty)
                             (X : Trace ty)
                             (G1 G2 : Env) (subS : Sub G S B)
                             (esub : subst_etvar G B S X G1 G2) {struct esub} :
  forall (Y : Index ty) (U : Ty),
  lookup_etvar G1 Y U -> Sub G2 (tsubstIndex X S Y) (tsubstTy X S U) :=
  match
    esub in (subst_etvar _ _ _ X0 G3 G4)
    return
      (forall (Y : Index ty) (U : Ty),
       lookup_etvar G3 Y U -> Sub G4 (tsubstIndex X0 S Y) (tsubstTy X0 S U))
  with
  | subst_etvar_here =>


      fun (Y : Index ty) (U : Ty) (lk : lookup_etvar (etvar G B) Y U) =>
      match
        lk in (lookup_etvar G' Y0 U0)
        return
          match G' return Prop with
          | etvar G0 B0 =>
              Sub G0 S B0 ->
              subst_etvar G0 B0 S X G1 G2 ->
              Sub G0 (tsubstIndex X0 S Y0) (tsubstTy X0 S U0)
          | _ => True
          end
      with
      | lookup_etvar_here G0 T46 _ =>
          fun (subS' : Sub G0 S T46) (_ : subst_etvar G0 T46 S X G1 G2) =>
          Sub_cast
            G0 S T46 G0 S (tsubstTy X0 S (tshiftTy C0 T46))
            eq_refl
            eq_refl
            (eq_sym (tsubstTy0_tshiftTy0_reflection T46 S))
            subS'
      | lookup_etvar_there_evar _ _ _ _ _ => I
      | lookup_etvar_there_etvar G0 X19 T46 T47 lk' =>
          fun (_ : Sub G0 S T47) (_ : subst_etvar G0 T47 S X G1 G2) =>
          Sub_cast G0 (tvar X19) T46 G0 (tvar X19)
            (tsubstTy X0 S (tshiftTy C0 T46)) eq_refl eq_refl
            (eq_sym (tsubstTy0_tshiftTy0_reflection T46 S))
            (Sub_var G0 X19 T46 lk')
      end subS esub



  | subst_etvar_there_evar X' G1' G2' T47 esub' =>


      fun (Y : Index ty) (U : Ty) (lk : lookup_etvar (evar G1' T47) Y U) =>
      match
        lk in (lookup_etvar G' Y0 U0)
        return
          match G' return Prop with
          | evar G1'0 T48 =>
              Sub G S B ->
              subst_etvar G B S X' G1'0 G2' ->
              Sub (evar G2' (tsubstTy X' S T48))
                (tsubstIndex (XS tm X') S Y0) (tsubstTy (XS tm X') S U0)
          | _ => True
          end
      with
      | lookup_etvar_here _ _ _ => I
      | lookup_etvar_there_evar G0 X19 T46 T0 lk' =>
          fun (subS' : Sub G S B) (esub'' : subst_etvar G B S X' G0 G2') =>
          shift_evar_Sub G2' (tsubstIndex (XS tm X') S X19)
            (tsubstTy (XS tm X') S T46)
            (Sub_cast G2' (tsubstIndex X' S X19) (tsubstTy X' S T46) G2'
               (tsubstIndex (XS tm X') S X19) (tsubstTy (XS tm X') S T46)
               eq_refl eq_refl (eq_sym (tsubstTy_tm T46 X' S))
               (subst_etvar_lookup_etvar G B S X' G0 G2' subS' esub'' X19 T46
                  lk')) C0 (evar G2' (tsubstTy X' S T0)) shift_evar_here
      | lookup_etvar_there_etvar _ _ _ _ _ => I
      end subS esub'




  | subst_etvar_there_etvar X' G1' G2' T47 esub' =>
      fun (Y : Index ty) (U : Ty) (lk : lookup_etvar (etvar G1' T47) Y U) =>
      match
        lk in (lookup_etvar G'' Y0 U0)
        return
          match G'' return Prop with
          | etvar G1'0 T48 =>
              forall (G0 : Env) (S0 B0 : Ty) (G2'0 : Env) (X'0 : Trace ty),
              Sub G0 S0 B0 ->
              subst_etvar G0 B0 S0 X'0 G1'0 G2'0 ->
              Sub (etvar G2'0 (tsubstTy X'0 S0 T48))
                (tsubstIndex (XS ty X'0) S0 Y0) (tsubstTy (XS ty X'0) S0 U0)
          | empty => True
          end
      with
      | lookup_etvar_here G1'' T46' wfT46' =>
          fun (G0 : Env) (S0 B0 : Ty) (G2'0 : Env)
            (X'0 : Trace ty) (subS0 : Sub G0 S0 B0)
            (esub'0 : subst_etvar G0 B0 S0 X'0 G1'' G2'0) =>
          Sub_cast (etvar G2'0 (tsubstTy X'0 S0 T46'))
            (tvar I0) (tshiftTy C0 (tsubstTy X'0 S0 T46'))
            (etvar G2'0 (tsubstTy X'0 S0 T46'))
            (tsubstIndex (XS ty X'0) S0 I0)
            (tsubstTy (XS ty X'0) S0 (tshiftTy C0 T46')) eq_refl eq_refl
            (eq_sym (tsubstTy_tshiftTy0_comm T46' X'0 S0))
            (Sub_var (etvar G2'0 (tsubstTy X'0 S0 T46')) I0
               (tshiftTy C0 (tsubstTy X'0 S0 T46'))
               (lookup_etvar_here
                  (substhvl_ty_wfTy (Sub_wf_0 G0 S0 B0 subS0)
                     (domainEnv G1'') T46' wfT46'
                     (subst_etvar_substhvl_ty esub'0))))
      | lookup_etvar_there_evar _ _ _ _ _ => I
      | lookup_etvar_there_etvar G1'' X19' T46' T47' lk' =>
          fun (G0 : Env) (S0 B0 : Ty) (G2'0 : Env)
            (X'0 : Trace ty) (subS0 : Sub G0 S0 B0)
            (esub'0 : subst_etvar G0 B0 S0 X'0 G1'' G2'0) =>
          Sub_cast (etvar G2'0 (tsubstTy X'0 S0 T47'))
            (tshiftTy C0 (tsubstIndex X'0 S0 X19'))
            (tshiftTy C0 (tsubstTy X'0 S0 T46'))
            (etvar G2'0 (tsubstTy X'0 S0 T47'))
            (tshiftTy C0 (tsubstIndex X'0 S0 X19'))
            (tsubstTy (XS ty X'0) S0 (tshiftTy C0 T46'))
            eq_refl
            eq_refl
            (eq_sym (tsubstTy_tshiftTy0_comm T46' X'0 S0))
            (shift_etvar_Sub G2'0 (tsubstIndex X'0 S0 X19')
               (tsubstTy X'0 S0 T46')
               (subst_etvar_lookup_etvar G0 B0 S0 X'0 G1'' G2'0 subS0 esub'0
                  X19' T46' lk') C0 (etvar G2'0 (tsubstTy X'0 S0 T47'))
               shift_etvar_here)
      end G S B G2' X' subS esub'
  end
     : forall (G : Env) (B S : Ty) (X : Trace ty) (G1 G2 : Env),
       Sub G S B ->
       subst_etvar G B S X G1 G2 ->
       forall (Y : Index ty) (U : Ty),
       lookup_etvar G1 Y U -> Sub G2 (tsubstIndex X S Y) (tsubstTy X S U)

Arguments G, B, S, X, G1, G2 are implicit and maximally inserted
-}
-}
