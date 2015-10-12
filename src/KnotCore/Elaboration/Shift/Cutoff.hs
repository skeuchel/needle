
module KnotCore.Elaboration.Shift.Cutoff where

import Control.Applicative

import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core

eCutoff :: Elab m => [NamespaceDecl] -> m Sentences
eCutoff nds =
  concat <$> sequence
   [ eFamilyCutoff
   , mapM (eFunctionWeakenCutoff . nsdTypeName) nds
   , pure [SentenceBlankline]
   , mapM (eLemmaWeakenCutoffAppend . nsdTypeName) nds
   --, mapM (eInstanceWeakenCutoff . nsdTypeName) nds
   ]

eFamilyCutoff :: Elab m => m Sentences
eFamilyCutoff = localNames $ do

  namespace <- idTypeNamespace
  a         <- freshVariable "a" =<< toRef namespace
  cutoffa   <- TermApp
               <$> (idFamilyCutoff >>= toRef)
               <*> sequence [toRef a]

  zero      <- idFamilyCutoffZero
  succ      <- idFamilyCutoffSucc

  sequence
    [ SentenceInductive . Inductive <$> sequence
      [ InductiveBody
        <$> idFamilyCutoff
        <*> sequence [ toBinder a ]
        <*> pure (TermSort Type)
        <*> sequence
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
      <*> sequence [BracedName <$> toName a],
      SentenceArguments
      <$> pure ModGlobal
      <*> toQualId succ
      <*> sequence [BracedName <$> toName a,
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

  rec       <-
    TermApp
    <$> toRef weaken
    <*> sequence [toRef cv, toRef k]

  nmEq <- Equation
          <$> (PatCtor <$> toQualId nm <*> pure [])
          <*> (TermApp
               <$> toRef succ
               <*> pure [rec]
              )
  nmWl <- Equation
          <$> pure PatUnderscore
          <*> pure rec

  nmMatch   <-
    TermMatch
    <$> (MatchItem <$> toRef a <*> pure Nothing <*> pure Nothing)
    <*> pure Nothing
    <*> pure (if single then [nmEq] else [nmEq,nmWl])

  SentenceFixpoint . Fixpoint <$> sequence
    [ FixpointBody
      <$> toId weaken
      <*> sequence [toBinder cv, toBinder k]
      <*> (Just . Struct <$> toId k)
      <*> typeCutoff (typeNameOf cv)
      <*> (TermMatch
           <$> (MatchItem
                <$> toRef k
                <*> pure Nothing
                <*> pure Nothing)
           <*> pure Nothing
           <*> sequence
               [ Equation
                 <$> (PatCtor <$> toQualId nil <*> pure [])
                 <*> toRef cv,
                 Equation
                 <$> (PatCtor
                      <$> toQualId cons
                      <*> sequence [toId a, toId k])
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
    <*> sequence
        [ TermApp
          <$> toRef weaken
          <*> sequence [toRef idx, toRef k1],
          toRef k2
        ]
  right <-
    TermApp
    <$> toRef weaken
    <*> sequence
        [ toRef idx,
          TermApp
          <$> toRef append
          <*> sequence [toRef k1, toRef k2]
        ]
  assertion <-
    TermForall
    <$> sequence [toBinder idx, toBinder k1, toBinder k2]
    <*> (TermEq <$> pure left <*> pure right)

  proof <- sequence
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
      <*> sequence [typeCutoff ntn]
      <*> pure [methodWeaken, methodAppend]

    return $ SentenceClassInst classInst
