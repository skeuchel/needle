
module KnotCore.Elaboration.SubstEnv where

import Control.Applicative
import Control.Monad

import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core


eSubstEnvs :: Elab m => [EnvDecl] -> m Sentences
eSubstEnvs eds =
  sequenceA
   [ eSubstEnv (typeNameOf bv) ed
   | ed <- eds
   , EnvCtorCons _cn bv _fds _mbRtn <- edCtors ed
   ]

eSubstEnv :: Elab m => NamespaceTypeName -> EnvDecl -> m Sentence
eSubstEnv ntn (EnvDecl etn _ ctors) = localNames $ do
  (stnSub,_)   <- getNamespaceCtor ntn

  x            <- freshTraceVar ntn
  t            <- freshSortVariable stnSub
  en           <- freshEnvVariable etn

  body <-
    FixpointBody
    <$> idFunctionSubstEnv ntn etn
    <*> sequenceA [toBinder x, toBinder t, toBinder en]
    <*> pure Nothing
    <*> toRef etn
    <*> (TermMatch
         <$> (MatchItem
              <$> toRef en
              <*> pure Nothing
              <*> pure Nothing)
         <*> pure Nothing
         <*> traverse (eEnvCtor x t) ctors
        )
  return . SentenceFixpoint $ Fixpoint [body]
  where
    eEnvCtor :: Elab m => TraceVar -> SortVariable -> EnvCtor -> m Equation
    eEnvCtor _ _ (EnvCtorNil cn) = localNames $
      Equation
        <$> (PatCtor
               <$> (Ident <$> toId cn)
               <*> pure [])
        <*> toRef cn
    eEnvCtor x t (EnvCtorCons cn bv fds _mbRtn) = localNames $ do
      en <- freshEnvVariable etn
      fs <- fieldDeclsToFields fds
      Equation
        <$> (PatCtor
               <$> (Ident <$> toId cn)
               <*> sequenceA (toId en : eFieldDeclIdentifiers fds)
            )
        <*> toTerm
            (ECons
               (ESubst (TVar x) (SVar t) (EVar en))
               (typeNameOf bv)
               (map (substField (TWeaken (TVar x) (HVDomainEnv (EVar en))) (SVar t)) fs)
            )
