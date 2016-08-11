{-# LANGUAGE GADTs #-}

module KnotCore.Elaboration.Shift.Cutoff where

import Control.Applicative

import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core

eCutoff :: Elab m => [NamespaceDecl] -> m Sentences
eCutoff nds =
  concat <$> sequenceA
   [ eFamilyCutoff
   , traverse (eFunctionWeakenCutoff . nsdTypeName) nds
   , pure [SentenceBlankline]
   , traverse (eLemmaWeakenCutoffAppend . nsdTypeName) nds
   --, traverse (eInstanceWeakenCutoff . nsdTypeName) nds
   ]

eFamilyCutoff :: Elab m => m Sentences
eFamilyCutoff = localNames $ do

  namespace <- idTypeNamespace
  a         <- freshVariable "a" =<< toRef namespace
  cutoffa   <- TermApp
               <$> (idFamilyCutoff >>= toRef)
               <*> sequenceA [toRef a]

  zero      <- idFamilyCutoffZero
  succ      <- idFamilyCutoffSucc

  sequenceA
    [ SentenceInductive . Inductive <$> sequenceA
      [ InductiveBody
        <$> idFamilyCutoff
        <*> sequenceA [ toBinder a ]
        <*> pure (TermSort Type)
        <*> sequenceA
            [ InductiveCtor
              <$> pure zero
              <*> pure []
              <*> pure Nothing,
              InductiveCtor
              <$> pure succ
              <*> pure []
              <*> pure (Just $ TermFunction cutoffa cutoffa)
            ]
      ],
      pure SentenceBlankline,
      SentenceArguments
      <$> pure ModGlobal
      <*> toQualId zero
      <*> sequenceA [BracedName <$> toName a],
      SentenceArguments
      <$> pure ModGlobal
      <*> toQualId succ
      <*> sequenceA [BracedName <$> toName a,
                    pure $ NormalName NameUnderscore
                   ]
    ]

eFunctionWeakenCutoff :: Elab m => NamespaceTypeName -> m Sentence
eFunctionWeakenCutoff ntn = localNames $ do

  namespace <- idTypeNamespace
  a         <- freshVariable "a" =<< toRef namespace

  nil       <- idCtorHVarlistNil
  cons      <- idCtorHVarlistCons

  nm        <- idCtorNamespace ntn
  succ      <- idFamilyCutoffSucc
  weaken    <- idFunctionWeakenCutoff ntn

  cv        <- freshCutoffVar ntn
  k         <- freshHVarlistVar
  single    <- hasSingleNamespace

  recursiveCall <-
    TermApp
    <$> toRef weaken
    <*> sequenceA [toRef cv, toRef k]

  nmEq <- Equation
          <$> (PatCtor <$> toQualId nm <*> pure [])
          <*> (TermApp
               <$> toRef succ
               <*> pure [recursiveCall]
              )
  nmWl <- Equation
          <$> pure PatUnderscore
          <*> pure recursiveCall

  nmMatch   <-
    TermMatch
    <$> (MatchItem <$> toRef a <*> pure Nothing <*> pure Nothing)
    <*> pure Nothing
    <*> pure (if single then [nmEq] else [nmEq,nmWl])

  SentenceFixpoint . Fixpoint <$> sequenceA
    [ FixpointBody
      <$> toId weaken
      <*> sequenceA [toBinder cv, toBinder k]
      <*> (Just . Struct <$> toId k)
      <*> typeCutoff (typeNameOf cv)
      <*> (TermMatch
           <$> (MatchItem
                <$> toRef k
                <*> pure Nothing
                <*> pure Nothing)
           <*> pure Nothing
           <*> sequenceA
               [ Equation
                 <$> (PatCtor <$> toQualId nil <*> pure [])
                 <*> toRef cv,
                 Equation
                 <$> (PatCtor
                      <$> toQualId cons
                      <*> sequenceA [toId a, toId k])
                 <*> pure nmMatch
               ]
          )
    ]

eLemmaWeakenCutoffAppend :: Elab m => NamespaceTypeName -> m Sentence
eLemmaWeakenCutoffAppend ntn = localNames $ do

  weakenAppend <- idLemmaWeakenCutoffAppend ntn
  weaken       <- idFunctionWeakenCutoff ntn
  append       <- idAppendHVarlist
  idx          <- freshCutoffVar ntn
  k1           <- freshHVarlistVar
  k2           <- freshHVarlistVar

  left <-
    TermApp
    <$> toRef weaken
    <*> sequenceA
        [ TermApp
          <$> toRef weaken
          <*> sequenceA [toRef idx, toRef k1],
          toRef k2
        ]
  right <-
    TermApp
    <$> toRef weaken
    <*> sequenceA
        [ toRef idx,
          TermApp
          <$> toRef append
          <*> sequenceA [toRef k1, toRef k2]
        ]
  assertion <-
    TermForall
    <$> sequenceA [toBinder idx, toBinder k1, toBinder k2]
    <*> (TermEq <$> pure left <*> pure right)

  proof <- sequenceA
    [ pure $ PrTactic "needleGenericWeakenAppend" []
    ]

  return $
    SentenceAssertionProof
      (Assertion AssLemma weakenAppend [] assertion)
      (ProofQed proof)

eInstanceWeakenCutoff :: Elab m => NamespaceTypeName -> m Sentence
eInstanceWeakenCutoff ntn = localNames $
  do
    insWeakenCutoff <- idInstanceWeakenCutoff ntn
    funWeakenCutoff <- idFunctionWeakenCutoff ntn
    lemWeakenAppend <- idLemmaWeakenCutoffAppend ntn

    weaken       <- idMethodWeaken
    weakenAppend <- idMethodWeakenAppend

    methodWeaken <-
      Method
      <$> toId weaken
      <*> pure []
      <*> toRef funWeakenCutoff

    methodAppend <-
      Method
      <$> toId weakenAppend
      <*> pure []
      <*> toRef lemWeakenAppend

    classInst <-
      ClassInstance insWeakenCutoff
      <$> pure []
      <*> idClassWeaken
      <*> sequenceA [typeCutoff ntn]
      <*> pure [methodWeaken, methodAppend]

    return $ SentenceClassInst classInst
