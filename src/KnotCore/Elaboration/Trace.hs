
module KnotCore.Elaboration.Trace where

import Control.Applicative

import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core

eTrace :: Elab m => [NamespaceDecl] -> m [Sentence]
eTrace _ =
  concat <$> sequenceA
  [ eFamilyTrace,
    sequenceA
    [ eFunctionWeakenTrace
    , eLemmaWeakenTraceAppend
    -- , eInstanceWeakenTrace
    ]
    {-
    traverse (eFunctionWeakenTrace . nsdTypeName) nds
    traverse (eInstanceWeakenTrace . nsdTypeName) nds
    -}
  ]

eFamilyTrace :: Elab m => m Sentences
eFamilyTrace = localNames $ do

  namespace <- idTypeNamespace
  a         <- freshVariable "a" =<< toRef namespace
  b         <- freshVariable "b" =<< toRef namespace
  tracea    <- TermApp
               <$> (idFamilyTrace >>= toRef)
               <*> sequenceA [toRef a]

  x0        <- idFamilyTraceNil
  xs        <- idFamilyTraceCons

  x         <- freshVariable "T" tracea

  sequenceA
    [ SentenceInductive . Inductive <$> sequenceA
        [ InductiveBody
          <$> idFamilyTrace
          <*> sequenceA [ toBinder a ]
          <*> pure (TermSort Type)
          <*> sequenceA
              [ InductiveCtor
                <$> toId x0
                <*> pure []
                <*> pure Nothing,
                InductiveCtor
                <$> toId xs
                <*> sequenceA [toBinder b, toBinder x]
                <*> pure Nothing
              ]
        ],
      pure SentenceBlankline,
      SentenceArguments
      <$> pure ModGlobal
      <*> toQualId x0
      <*> sequenceA [BracketedName <$> toName a],
      SentenceArguments
      <$> pure ModGlobal
      <*> toQualId xs
      <*> sequenceA [BracketedName <$> toName a,
                    NormalName <$> toName b,
                    pure $ NormalName NameUnderscore
                   ]
    ]

eFunctionWeakenTrace :: Elab m => m Sentence
eFunctionWeakenTrace = localNames $ do

  namespace <- idTypeNamespace
  a         <- freshVariable "a" =<< toRef namespace
  b         <- freshVariable "b" =<< toRef namespace
  tracea    <- TermApp
               <$> (idFamilyTrace >>= toRef)
               <*> sequenceA [toRef a]

  weaken    <- idFunctionWeakenTrace
  h0        <- idCtorHVarlistNil
  hs        <- idCtorHVarlistCons
  xs        <- idFamilyTraceCons

  x         <- freshVariable "x" tracea
  k         <- freshHVarlistVar

  SentenceFixpoint . Fixpoint <$> sequenceA
    [ FixpointBody
      <$> toId weaken
      <*> sequenceA [toImplicitBinder a, toBinder x, toBinder k]
      <*> (Just . Struct <$> toId k)
      <*> pure tracea
      <*> (TermMatch
           <$> (MatchItem
                <$> toRef k
                <*> pure Nothing
                <*> pure Nothing)
           <*> pure Nothing
           <*> sequenceA
               [ Equation
                 <$> (PatCtor <$> toQualId h0 <*> pure [])
                 <*> toRef x,
                 Equation
                 <$> (PatCtor
                      <$> toQualId hs
                      <*> sequenceA [toId b, toId k])
                 <*> (TermApp
                      <$> toRef xs
                      <*> sequenceA
                          [ toRef b,
                            TermApp
                            <$> toRef weaken
                            <*> sequenceA [toRef x, toRef k]
                          ]
                     )
               ]
          )
    ]

eLemmaWeakenTraceAppend :: Elab m => m Sentence
eLemmaWeakenTraceAppend = localNames $ do

  namespace    <- idTypeNamespace
  a            <- freshVariable "a" =<< toRef namespace
  tracea       <- TermApp
                  <$> (idFamilyTrace >>= toRef)
                  <*> sequenceA [toRef a]

  weakenAppend <- idLemmaWeakenTraceAppend
  weaken       <- idFunctionWeakenTrace
  append       <- idAppendHVarlist
  x            <- freshVariable "x" tracea
  k1           <- freshHVarlistVar
  k2           <- freshHVarlistVar

  left <-
    TermApp
    <$> toRef weaken
    <*> sequenceA
        [ TermApp
          <$> toRef weaken
          <*> sequenceA [toRef x, toRef k1],
          toRef k2
        ]
  right <-
    TermApp
    <$> toRef weaken
    <*> sequenceA
        [ toRef x,
          TermApp
          <$> toRef append
          <*> sequenceA [toRef k1, toRef k2]
        ]

  assertion <-
    TermForall
    <$> sequenceA [toBinder x, toBinder k1, toBinder k2]
    <*> (TermEq <$> pure left <*> pure right)

  proof <- sequenceA
    [ pure $ PrTactic "needleGenericWeakenAppend" []
    ]

  aIntro <- toBinder a
  return $
    SentenceAssertionProof
      (Assertion AssLemma weakenAppend [aIntro] assertion)
      (ProofQed proof)

eInstanceWeakenTrace :: Elab m => m Sentence
eInstanceWeakenTrace = localNames $ do

  insWeakenTrace  <- idInstanceWeakenTrace
  funWeakenTrace  <- idFunctionWeakenTrace
  lemWeakenAppend <- idLemmaWeakenTraceAppend

  namespace    <- idTypeNamespace
  a            <- freshVariable "a" =<< toRef namespace
  tracea       <- TermApp
                  <$> (idFamilyTrace >>= toRef)
                  <*> sequenceA [toRef a]

  weaken       <- idMethodWeaken
  weakenAppend <- idMethodWeakenAppend

  methodWeaken <-
    Method
    <$> toId weaken
    <*> pure []
    <*> (TermApp
         <$> toRef funWeakenTrace
         <*> sequenceA [toRef a]
        )

  methodAppend <-
    Method
    <$> toId weakenAppend
    <*> pure []
    <*> (TermApp
         <$> toRef lemWeakenAppend
         <*> sequenceA [toRef a]
        )

  classInst <-
    ClassInstance insWeakenTrace
    <$> sequenceA [toBinder a]
    <*> idClassWeaken
    <*> pure [tracea]
    <*> pure [methodWeaken, methodAppend]

  return $ SentenceClassInst classInst
