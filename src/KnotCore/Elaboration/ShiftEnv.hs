
module KnotCore.Elaboration.ShiftEnv where

import Control.Applicative
import Control.Monad

import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core


eShiftEnvs :: Elab m => [EnvDecl] -> m Sentences
eShiftEnvs eds =
  sequence
   [ eShiftEnv (typeNameOf mv) ed
   | ed <- eds
   , EnvCtorCons _ mv _ <- edCtors ed
   ]

eShiftEnv :: Elab m => NamespaceTypeName -> EnvDecl -> m Sentence
eShiftEnv ntn (EnvDecl etn _ ctors) = localNames $ do
  c  <- freshCutoffVar ntn
  en <- freshEnvVar etn
  body <-
    FixpointBody
    <$> idFunctionShiftEnv ntn etn
    <*> sequence [toBinder c, toBinder en]
    <*> pure Nothing
    <*> toRef etn
    <*> (TermMatch
         <$> (MatchItem
              <$> toRef en
              <*> pure Nothing
              <*> pure Nothing)
         <*> pure Nothing
         <*> mapM (eEnvCtor c) ctors
        )
  return . SentenceFixpoint $ Fixpoint [body]
  where
    eEnvCtor :: Elab m => CutoffVar -> EnvCtor -> m Equation
    eEnvCtor _ (EnvCtorNil cn) = localNames $ do
      Equation
        <$> (PatCtor
               <$> (Ident <$> toId cn)
               <*> pure [])
        <*> toRef cn
    eEnvCtor c (EnvCtorCons cn _ fields) = localNames $ do
      en <- freshEnvVar etn
      Equation
        <$> (PatCtor
               <$> (Ident <$> toId cn)
               <*> sequence (toId en : map toId fields))
        <*> toTerm (ECtor cn
                      (EShift (CVar c) (EVar en))
                      (map (SShift' (CWeaken (CVar c) (HVDomainEnv (EVar en))) . SVar) fields))
