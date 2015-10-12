
module KnotCore.Elaboration.Trace where

import Control.Applicative

import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core

eTrace :: Elab m => [NamespaceDecl] -> m [Sentence]
eTrace _ =
  concat <$> sequence
  [ eFamilyTrace,
    sequence
    [ eFunctionWeakenTrace
    , eLemmaWeakenTraceAppend
    -- , eInstanceWeakenTrace
    ]
    {-
    mapM (eFunctionWeakenTrace . nsdTypeName) nds
    mapM (eInstanceWeakenTrace . nsdTypeName) nds
    -}
  ]

eFamilyTrace :: Elab m => m Sentences
eFamilyTrace = localNames $ do

  namespace <- idTypeNamespace
  a         <- freshVariable "a" =<< toRef namespace
  b         <- freshVariable "b" =<< toRef namespace
  tracea    <- TermApp
               <$> (idFamilyTrace >>= toRef)
               <*> sequence [toRef a]

  x0        <- idFamilyTraceNil
  xs        <- idFamilyTraceCons

  x         <- freshVariable "T" tracea

  sequence
    [ SentenceInductive . Inductive <$> sequence
        [ InductiveBody
          <$> idFamilyTrace
          <*> sequence [ toBinder a ]
          <*> pure (TermSort Type)
          <*> sequence
              [ InductiveCtor
                <$> toId x0
                <*> pure []
                <*> pure Nothing,
                InductiveCtor
                <$> toId xs
                <*> sequence [toBinder b, toBinder x]
                <*> pure Nothing
              ]
        ],
      pure SentenceBlankline,
      SentenceArguments
      <$> pure ModGlobal
      <*> toQualId x0
      <*> sequence [BracketedName <$> toName a],
      SentenceArguments
      <$> pure ModGlobal
      <*> toQualId xs
      <*> sequence [BracketedName <$> toName a,
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
               <*> sequence [toRef a]

  weaken    <- idFunctionWeakenTrace
  h0        <- idCtorHVarlistNil
  hs        <- idCtorHVarlistCons
  xs        <- idFamilyTraceCons

  x         <- freshVariable "x" tracea
  k         <- freshHVarlistVar

  SentenceFixpoint . Fixpoint <$> sequence
    [ FixpointBody
      <$> toId weaken
      <*> sequence [toImplicitBinder a, toBinder x, toBinder k]
      <*> (Just . Struct <$> toId k)
      <*> pure tracea
      <*> (TermMatch
           <$> (MatchItem
                <$> toRef k
                <*> pure Nothing
                <*> pure Nothing)
           <*> pure Nothing
           <*> sequence
               [ Equation
                 <$> (PatCtor <$> toQualId h0 <*> pure [])
                 <*> toRef x,
                 Equation
                 <$> (PatCtor
                      <$> toQualId hs
                      <*> sequence [toId b, toId k])
                 <*> (TermApp
                      <$> toRef xs
                      <*> sequence
                          [ toRef b,
                            TermApp
                            <$> toRef weaken
                            <*> sequence [toRef x, toRef k]
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
                  <*> sequence [toRef a]

  weakenAppend <- idLemmaWeakenTraceAppend
  weaken       <- idFunctionWeakenTrace
  append       <- idAppendHVarlist
  x            <- freshVariable "x" tracea
  k1           <- freshHVarlistVar
  k2           <- freshHVarlistVar

  left <-
    TermApp
    <$> toRef weaken
    <*> sequence
        [ TermApp
          <$> toRef weaken
          <*> sequence [toRef x, toRef k1],
          toRef k2
        ]
  right <-
    TermApp
    <$> toRef weaken
    <*> sequence
        [ toRef x,
          TermApp
          <$> toRef append
          <*> sequence [toRef k1, toRef k2]
        ]

  assertion <-
    TermForall
    <$> sequence [toBinder x, toBinder k1, toBinder k2]
    <*> (TermEq <$> pure left <*> pure right)

  proof <- sequence
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
                  <*> sequence [toRef a]

  weaken       <- idMethodWeaken
  weakenAppend <- idMethodWeakenAppend

  methodWeaken <-
    Method
    <$> toId weaken
    <*> pure []
    <*> (TermApp
         <$> toRef funWeakenTrace
         <*> sequence [toRef a]
        )

  methodAppend <-
    Method
    <$> toId weakenAppend
    <*> pure []
    <*> (TermApp
         <$> toRef lemWeakenAppend
         <*> sequence [toRef a]
        )

  classInst <-
    ClassInstance insWeakenTrace
    <$> sequence [toBinder a]
    <*> idClassWeaken
    <*> pure [tracea]
    <*> pure [methodWeaken, methodAppend]

  return $ SentenceClassInst classInst
