
module KnotCore.Elaboration.Index where

import Control.Applicative

import Coq.Syntax
import Coq.StdLib

import KnotCore.Syntax
import KnotCore.Elaboration.Core

eIndex :: Elab m => [NamespaceDecl] -> m Sentences
eIndex nds =
  concat <$> sequenceA
    [ eTypeIndex
    , sequenceA
      [ pure SentenceBlankline
      , eEqIndexDec
      , pure SentenceBlankline
      ]
    , traverse (eFunctionWeakenIndex . nsdTypeName) nds
    , traverse (eLemmaWeakenIndexAppend . nsdTypeName) nds
    -- , traverse (eInstanceWeakenIndex . nsdTypeName) nds
    ]

eTypeIndex :: Elab m => m Sentences
eTypeIndex = localNames $ do
  namespace <- idTypeNamespace
  a         <- freshVariable "a" =<< toRef namespace
  indexa    <- TermApp
               <$> (idFamilyIndex >>= toRef)
               <*> sequenceA [toRef a]
  sequenceA
    [ SentenceInductive . Inductive <$> sequenceA
      [ InductiveBody
        <$> idFamilyIndex
        <*> sequenceA [ toBinder a ]
        <*> pure (TermSort Type)
        <*> sequenceA
            [ InductiveCtor
              <$> idFamilyIndexZero
              <*> pure []
              <*> pure Nothing,
              InductiveCtor
              <$> idFamilyIndexSucc
              <*> pure []
              <*> pure (Just $ TermFunction indexa indexa)
            ]
      ],
      pure SentenceBlankline,
      SentenceArguments
      <$> pure ModGlobal
      <*> (idFamilyIndexZero >>= toQualId)
      <*> sequenceA [BracketedName <$> toName a],
      SentenceArguments
      <$> pure ModGlobal
      <*> (idFamilyIndexSucc >>= toQualId)
      <*> sequenceA [BracketedName <$> toName a,
                    pure $ NormalName NameUnderscore
                   ]
    ]


eEqIndexDec :: Elab m => m Sentence
eEqIndexDec = localNames $ do

  lem       <- idLemmaEqIndexDec

  namespace <- idTypeNamespace
  a         <- freshVariable "a" =<< toRef namespace
  indexa    <- TermApp
               <$> (idFamilyIndex >>= toRef)
               <*> sequenceA [toRef a]

  i         <- freshVariable "i" indexa
  j         <- freshVariable "j" indexa
  binders   <- sequenceA [toImplicitBinder a, toBinder i, toBinder j]
  eq_ij     <- eq <$> toRef i <*> toRef j

  let assertion = sumbool eq_ij (Coq.StdLib.not eq_ij)
      proof = [PrTactic "decide equality" []]

  return $
    SentenceAssertionProof
      (Assertion AssLemma lem binders assertion)
      (ProofQed proof)


eFunctionWeakenIndex :: Elab m => NamespaceTypeName -> m Sentence
eFunctionWeakenIndex ntn = localNames $ do

  namespace <- idTypeNamespace
  a         <- freshVariable "a" =<< toRef namespace

  nil       <- idCtorHVarlistNil
  cons      <- idCtorHVarlistCons

  nm        <- idCtorNamespace ntn
  succ      <- idFamilyIndexSucc
  weaken    <- idFunctionWeakenIndex ntn

  idx       <- freshIndexVar ntn
  k         <- freshHVarlistVar
  single    <- hasSingleNamespace

  recursiveCall <-
    TermApp
    <$> toRef weaken
    <*> sequenceA [toRef idx, toRef k]

  nmEq <- Equation
          <$> (PatCtor <$> toQualId nm <*> pure [])
          <*> (TermApp
               <$> toRef succ
               <*> pure [recursiveCall]
              )
  nmWl <- Equation
          <$> pure PatUnderscore
          <*> pure recursiveCall
  nmMatch <-
    TermMatch
    <$> (MatchItem <$> toRef a <*> pure Nothing <*> pure Nothing)
    <*> pure Nothing
    <*> pure (if single then [nmEq] else [nmEq,nmWl])

  SentenceFixpoint . Fixpoint <$> sequenceA
    [ FixpointBody
      <$> toId weaken
      <*> sequenceA [toBinder idx, toBinder k]
      <*> (Just . Struct <$> toId k)
      <*> typeIndex (typeNameOf idx)
      <*> (TermMatch
           <$> (MatchItem
                <$> toRef k
                <*> pure Nothing
                <*> pure Nothing)
           <*> pure Nothing
           <*> sequenceA
               [ Equation
                 <$> (PatCtor <$> toQualId nil <*> pure [])
                 <*> toRef idx,
                 Equation
                 <$> (PatCtor
                      <$> toQualId cons
                      <*> sequenceA [toId a, toId k])
                 <*> pure nmMatch
               ]
          )
    ]

eLemmaWeakenIndexAppend :: Elab m => NamespaceTypeName -> m Sentence
eLemmaWeakenIndexAppend ntn = localNames $ do

  weakenAppend <- idLemmaWeakenIndexAppend ntn
  weaken       <- idFunctionWeakenIndex ntn
  append       <- idAppendHVarlist
  idx          <- freshIndexVar ntn
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

eInstanceWeakenIndex :: Elab m => NamespaceTypeName -> m Sentence
eInstanceWeakenIndex ntn = localNames $ do

  insWeakenIndex  <- idInstanceWeakenIndex ntn
  funWeakenIndex  <- idFunctionWeakenIndex ntn
  lemWeakenAppend <- idLemmaWeakenIndexAppend ntn

  weaken       <- idMethodWeaken
  weakenAppend <- idMethodWeakenAppend

  methodWeaken <-
    Method
    <$> toId weaken
    <*> pure []
    <*> toRef funWeakenIndex

  methodAppend <-
    Method
    <$> toId weakenAppend
    <*> pure []
    <*> toRef lemWeakenAppend

  classInst <-
    ClassInstance insWeakenIndex
    <$> pure []
    <*> idClassWeaken
    <*> sequenceA [typeIndex ntn]
    <*> pure [methodWeaken, methodAppend]

  return $ SentenceClassInst classInst
