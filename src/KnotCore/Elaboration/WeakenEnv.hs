
module KnotCore.Elaboration.WeakenEnv where

import Control.Applicative
import Control.Monad

import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core

eFunctionWeakenEnv :: Elab m => EnvTypeName -> m Sentence
eFunctionWeakenEnv etn = localNames $ do

  weaken    <- idFunctionWeakenEnv etn
  t         <- freshEnvVariable etn
  k         <- freshHVarlistVar

  nil       <- idCtorHVarlistNil
  cons      <- idCtorHVarlistCons

  deps      <- getEnvNamespaceDependencies etn
  ntns      <- getNamespaces

  c0        <- idFamilyCutoffZero

  recursiveCall <-
    TermApp
    <$> toRef weaken
    <*> sequenceA [toRef t, toRef k]

  eq_h0 <-
    Equation
    <$> (PatCtor <$> toQualId nil <*> pure [])
    <*> toRef t

  eq_hs <- for ntns $ \ntn ->
    Equation
    <$> (PatCtor <$> toQualId cons <*> sequenceA [toId ntn, toId k])
    <*> (if ntn `elem` deps
         then TermApp
              <$> (idFunctionShiftEnv ntn etn >>= toRef)
              <*> sequenceA [ toRef c0, pure recursiveCall ]
         else pure recursiveCall
        )

  SentenceFixpoint . Fixpoint <$> sequenceA
    [ FixpointBody
      <$> toId weaken
      <*> sequenceA [toBinder t, toBinder k]
      <*> (Just . Struct <$> toId k)
      <*> toRef etn
      <*> (TermMatch
           <$> (MatchItem
                <$> toRef k
                <*> pure Nothing
                <*> pure Nothing)
           <*> pure Nothing
           <*> pure (eq_h0:eq_hs)
          )
    ]
