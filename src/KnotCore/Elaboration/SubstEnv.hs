
module KnotCore.Elaboration.SubstEnv where

import Control.Applicative
import Control.Monad

import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core


eSubstEnvs :: Elab m => [EnvDecl] -> m Sentences
eSubstEnvs eds =
  sequence
   [ eSubstEnv (typeNameOf mv) ed
   | ed <- eds
   , EnvCtorCons _ mv _ <- edCtors ed
   ]

eSubstEnv :: Elab m => NamespaceTypeName -> EnvDecl -> m Sentence
eSubstEnv ntn (EnvDecl etn _ ctors) = localNames $ do
  (stnSub,_)   <- getNamespaceCtor ntn

  x            <- freshTraceVar ntn
  t            <- freshSubtreeVar stnSub
  en           <- freshEnvVar etn

  body <-
    FixpointBody
    <$> idFunctionSubstEnv ntn etn
    <*> sequence [toBinder x, toBinder t, toBinder en]
    <*> pure Nothing
    <*> toRef etn
    <*> (TermMatch
         <$> (MatchItem
              <$> toRef en
              <*> pure Nothing
              <*> pure Nothing)
         <*> pure Nothing
         <*> mapM (eEnvCtor x t) ctors
        )
  return . SentenceFixpoint $ Fixpoint [body]
  where
    eEnvCtor :: Elab m => TraceVar -> SubtreeVar -> EnvCtor -> m Equation
    eEnvCtor _ _ (EnvCtorNil cn) = localNames $ do
      Equation
        <$> (PatCtor
               <$> (Ident <$> toId cn)
               <*> pure [])
        <*> toRef cn
    eEnvCtor x t (EnvCtorCons cn _ fields) = localNames $ do
      en <- freshEnvVar etn
      Equation
        <$> (PatCtor
               <$> (Ident <$> toId cn)
               <*> sequence (toId en : map toId fields))
        <*> toTerm (ECtor cn
                      (ESubst (TVar x) (SVar t) (EVar en))
                      (map (SSubst' (TWeaken (TVar x) (HVDomainEnv (EVar en))) (SVar t) . SVar) fields))
