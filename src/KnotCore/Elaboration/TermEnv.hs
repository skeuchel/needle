
module KnotCore.Elaboration.TermEnv where

import Control.Applicative
import Control.Monad

import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core

eEnvDecl :: Elab m => EnvDecl -> m Sentence
eEnvDecl (EnvDecl etn _ ctors) = localNames $ do

  ev <- freshEnvVar etn

  ctors <- forM ctors $ \cn ->
    case cn of
      EnvCtorNil cn ->
        InductiveCtor
          <$> toId cn
          <*> pure []
          <*> pure Nothing
      EnvCtorCons cn _ fields ->
        InductiveCtor
          <$> toId cn
          <*> sequence (toBinder ev : map toBinder fields)
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
    en1 <- freshEnvVar etn
    en2 <- freshEnvVar etn
    fmap (SentenceFixpoint .
          Fixpoint . (:[])) $
      FixpointBody
        <$> idFunctionAppendEnv etn
        <*> sequence [toBinder en1, toBinder en2]
        <*> pure Nothing
        <*> toRef etn
        <*> (TermMatch
               <$> (MatchItem
                      <$> toRef en2
                      <*> pure Nothing
                      <*> pure Nothing)
               <*> pure Nothing
               <*> mapM (eEnvAppendCtor en1) ctors
            )
  where
    eEnvAppendCtor :: Elab m => EnvVar -> EnvCtor -> m Equation
    eEnvAppendCtor en1 (EnvCtorNil cn) = localNames $
      do
        Equation
          <$> (PatCtor
                 <$> (Ident <$> toId cn)
                 <*> pure [])
          <*> toRef en1
    eEnvAppendCtor en1 (EnvCtorCons cn _ fields) = localNames $
      do
        en3 <- freshEnvVar etn
        Equation
          <$> (PatCtor
                 <$> (Ident <$> toId cn)
                 <*> sequence (toId en3 : map toId fields))
          <*> (TermApp
                 <$> toRef cn
                 <*> sequence ((TermApp
                                  <$> (idFunctionAppendEnv etn >>= toRef)
                                  <*> sequence [ toRef en1, toRef en3 ]
                               ) : map toRef fields)
              )


eEnvLength:: Elab m => EnvDecl -> m Sentence
eEnvLength (EnvDecl etn _ ctors) = localNames $ do
  en <- freshEnvVar etn
  body <-
    FixpointBody
    <$> idFunctionDomainEnv etn
    <*> sequence [toBinder en]
    <*> pure Nothing
    <*> (idTypeHVarlist >>= toRef)
    <*> (TermMatch
         <$> (MatchItem
              <$> toRef en
              <*> pure Nothing
              <*> pure Nothing)
         <*> pure Nothing
         <*> mapM eEnvLengthCtor ctors
        )
  return . SentenceFixpoint $ Fixpoint [body]
  where
    eEnvLengthCtor :: Elab m => EnvCtor -> m Equation
    eEnvLengthCtor (EnvCtorNil cn) = localNames $ do
      Equation
        <$> (PatCtor
               <$> (Ident <$> toId cn)
               <*> pure [])
        <*> toTerm HV0
    eEnvLengthCtor (EnvCtorCons cn mv fields) = localNames $ do
      en <- freshEnvVar etn
      Equation
        <$> (PatCtor
               <$> (Ident <$> toId cn)
               <*> sequence (toId en : map toId fields))
        <*> (TermApp
               <$> (idCtorHVarlistCons >>= toRef)
               <*> sequence
                   [toRef (typeNameOf mv),
                    (TermApp
                     <$> (idFunctionDomainEnv etn >>= toRef)
                     <*> sequence [ toRef en ]
                    )
                   ]
            )
