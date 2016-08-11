
module KnotCore.Elaboration.TermEnv where

import Control.Applicative
import Control.Monad

import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core

eEnvDecl :: Elab m => EnvDecl -> m Sentence
eEnvDecl (EnvDecl etn _ ctors) = localNames $ do

  ev <- freshEnvVariable etn

  ctors <- for ctors $ \cn ->
    case cn of
      EnvCtorNil cn ->
        InductiveCtor
          <$> toId cn
          <*> pure []
          <*> pure Nothing
      EnvCtorCons cn _ fields _mbRtn ->
        InductiveCtor
          <$> toId cn
          <*> sequenceA (toBinder ev : eFieldDeclBinders fields)
          <*> pure Nothing

  body <-
    InductiveBody
    <$> toId etn
    <*> pure []
    <*> pure (TermSort Type)
    <*> pure ctors

  return (SentenceInductive $ Inductive [body])

eEnvAppend :: Elab m => EnvDecl -> m Sentence
eEnvAppend (EnvDecl etn _ ctors) = localNames $
  do
    en1 <- freshEnvVariable etn
    en2 <- freshEnvVariable etn
    fmap (SentenceFixpoint .
          Fixpoint . (:[])) $
      FixpointBody
        <$> idFunctionAppendEnv etn
        <*> sequenceA [toBinder en1, toBinder en2]
        <*> pure Nothing
        <*> toRef etn
        <*> (TermMatch
               <$> (MatchItem
                      <$> toRef en2
                      <*> pure Nothing
                      <*> pure Nothing)
               <*> pure Nothing
               <*> traverse (eEnvAppendCtor en1) ctors
            )
  where
    eEnvAppendCtor :: Elab m => EnvVariable -> EnvCtor -> m Equation
    eEnvAppendCtor ev1 (EnvCtorNil cn) = localNames $
      Equation
        <$> (PatCtor
               <$> (Ident <$> toId cn)
               <*> pure [])
        <*> toRef ev1
    eEnvAppendCtor ev1 (EnvCtorCons cn _ fields _mbRtn) = localNames $
      do
        ev3 <- freshEnvVariable etn
        Equation
          <$> (PatCtor
                 <$> (Ident <$> toId cn)
                 <*> sequenceA (toId ev3 : eFieldDeclIdentifiers fields)
              )
          <*> (TermApp
                 <$> toRef cn
                 <*> ((:)
                        <$> (TermApp
                             <$> (idFunctionAppendEnv etn >>= toRef)
                             <*> sequenceA [ toRef ev1, toRef ev3 ]
                            )
                        <*> sequenceA (eFieldDeclRefs fields)
                     )
              )


eEnvLength:: Elab m => EnvDecl -> m Sentence
eEnvLength (EnvDecl etn _ ctors) = localNames $ do
  en <- freshEnvVariable etn
  body <-
    FixpointBody
    <$> idFunctionDomainEnv etn
    <*> sequenceA [toBinder en]
    <*> pure Nothing
    <*> (idTypeHVarlist >>= toRef)
    <*> (TermMatch
         <$> (MatchItem
              <$> toRef en
              <*> pure Nothing
              <*> pure Nothing)
         <*> pure Nothing
         <*> traverse eEnvLengthCtor ctors
        )
  return . SentenceFixpoint $ Fixpoint [body]
  where
    eEnvLengthCtor :: Elab m => EnvCtor -> m Equation
    eEnvLengthCtor (EnvCtorNil cn) = localNames $
      Equation
        <$> (PatCtor
               <$> (Ident <$> toId cn)
               <*> pure [])
        <*> toTerm HV0
    eEnvLengthCtor (EnvCtorCons cn mv fields _mbRtn) = localNames $ do
      en <- freshEnvVariable etn
      Equation
        <$> (PatCtor
               <$> (Ident <$> toId cn)
               <*> sequenceA (toId en :eFieldDeclIdentifiers fields)
            )
        <*> (TermApp
               <$> (idCtorHVarlistCons >>= toRef)
               <*> sequenceA
                   [ toRef (typeNameOf mv),
                     TermApp
                      <$> (idFunctionDomainEnv etn >>= toRef)
                      <*> sequenceA [ toRef en ]
                   ]
            )
