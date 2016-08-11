
module KnotCore.Elaboration.ShiftEnv where

import Control.Applicative
import Control.Monad

import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core


eShiftEnvs :: Elab m => [EnvDecl] -> m Sentences
eShiftEnvs eds =
  sequenceA
   [ eShiftEnv (typeNameOf mv) ed
   | ed <- eds
   , EnvCtorCons _ mv _ _ <- edCtors ed
   ]

eShiftEnv :: Elab m => NamespaceTypeName -> EnvDecl -> m Sentence
eShiftEnv ntn (EnvDecl etn _ ctors) = localNames $ do
  c  <- freshCutoffVar ntn
  en <- freshEnvVariable etn
  body <-
    FixpointBody
    <$> idFunctionShiftEnv ntn etn
    <*> sequenceA [toBinder c, toBinder en]
    <*> pure Nothing
    <*> toRef etn
    <*> (TermMatch
         <$> (MatchItem
              <$> toRef en
              <*> pure Nothing
              <*> pure Nothing)
         <*> pure Nothing
         <*> traverse (eEnvCtor c) ctors
        )
  return . SentenceFixpoint $ Fixpoint [body]
  where
    eEnvCtor :: Elab m => CutoffVar -> EnvCtor -> m Equation
    eEnvCtor _ (EnvCtorNil cn) = localNames $
      Equation
        <$> (PatCtor
               <$> (Ident <$> toId cn)
               <*> pure [])
        <*> toRef cn
    eEnvCtor c (EnvCtorCons cn bv fds _mbRtn) = localNames $ do
      en <- freshEnvVariable etn
      fs <- fieldDeclsToFields fds
      Equation
        <$> (PatCtor
               <$> (Ident <$> toId cn)
               <*> sequenceA (toId en : eFieldDeclIdentifiers fds)
            )
        <*> toTerm
            (ECons
               (EShift (CVar c) (EVar en))
               (typeNameOf bv)
               (map (shiftField (CWeaken (CVar c) (HVDomainEnv (EVar en)))) fs)
            )
