
module KnotCore.Elaboration.Weaken.WeakenTerm where

import Control.Applicative
import Control.Monad

import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core

eFunctionWeakenTerm :: Elab m => SortTypeName -> m Sentence
eFunctionWeakenTerm stn = localNames $ do

  weaken    <- idFunctionWeakenTerm stn
  t         <- freshSubtreeVar stn
  k         <- freshHVarlistVar

  nil       <- idCtorHVarlistNil
  cons      <- idCtorHVarlistCons

  deps      <- getSortNamespaceDependencies stn
  ntns      <- getNamespaces

  c0        <- idFamilyCutoffZero

  rec       <-
    TermApp
    <$> toRef weaken
    <*> sequence [toRef t, toRef k]

  eq_h0 <-
    Equation
    <$> (PatCtor <$> toQualId nil <*> pure [])
    <*> toRef t

  eq_hs <- forM ntns $ \ntn ->
    Equation
    <$> (PatCtor <$> toQualId cons <*> sequence [toId ntn, toId k])
    <*> (if ntn `elem` deps
         then TermApp
              <$> (idFunctionShift ntn stn >>= toRef)
              <*> sequence [ toRef c0, pure rec ]
         else pure rec
        )

  SentenceFixpoint . Fixpoint <$> sequence
    [ FixpointBody
      <$> toId weaken
      <*> sequence [toBinder t, toBinder k]
      <*> (Just . Struct <$> toId k)
      <*> toRef stn
      <*> (TermMatch
           <$> (MatchItem
                <$> toRef k
                <*> pure Nothing
                <*> pure Nothing)
           <*> pure Nothing
           <*> pure (eq_h0:eq_hs)
          )
    ]

{-
eLemmaWeakenIndexAppend :: Elab m => SortTypeName -> m Sentence
eLemmaWeakenIndexAppend stn = localNames $ do

  weakenAppend <- idLemmaWeakenIndexAppend ntn
  weaken       <- idFunctionWeakenIndex ntn
  append       <- idAppendHVarlist
  idx          <- freshIndexVar ntn
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
    <*> sequence [typeIndex ntn]
    <*> pure [methodWeaken, methodAppend]

  return $ SentenceClassInst classInst
-}
