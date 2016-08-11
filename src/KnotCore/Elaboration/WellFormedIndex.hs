
module KnotCore.Elaboration.WellFormedIndex where

import Control.Applicative
import Data.Maybe

import Coq.StdLib
import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core

eWellFormedIndex :: Elab m => m Sentence
eWellFormedIndex = localNames $ do
  wfindex   <- idFunctionWellFormedIndex

  namespace <- idTypeNamespace
  a         <- freshVariable "a" =<< toRef namespace
  b         <- freshVariable "b" =<< toRef namespace
  indexa    <- TermApp
               <$> (idFamilyIndex >>= toRef)
               <*> sequenceA [toRef a]

  k         <- freshHVarlistVar
  h0        <- idCtorHVarlistNil
  hs        <- idCtorHVarlistCons

  i0        <- idFamilyIndexZero
  is        <- idFamilyIndexSucc
  i         <- freshVariable "i" indexa

  eq_ab     <- eq <$> toRef a <*> toRef b
  e         <- freshVariable "e" eq_ab
  n         <- freshVariable "n" (Coq.StdLib.not eq_ab)

  binders <- sequenceA [toImplicitBinder a, toBinder k, toBinder i]
  anno    <- Just . Struct <$> toId k

  recursiveCall <-
    TermApp
    <$> toRef wfindex
    <*> sequenceA [toRef k, toRef i]

  innerMatch <-
    TermMatch
    <$> (MatchItem
         <$> toRef i
         <*> pure Nothing
         <*> pure Nothing
        )
    <*> pure Nothing
    <*> sequenceA
        [ Equation
          <$> (PatCtor <$> toQualId i0 <*> pure [])
          <*> pure true
        , Equation
          <$> (PatCtor <$> toQualId is <*> sequenceA [toId i])
          <*> pure recursiveCall
        ]

  namespaceMatch <-
    TermMatch
    <$> (MatchItem
         <$> (TermApp
              <$> (idLemmaEqNamespaceDec >>= toRef)
              <*> sequenceA [ toRef a, toRef b ]
             )
         <*> pure Nothing
         <*> pure Nothing
        )
    <*> pure Nothing
    <*> sequenceA
        [ Equation
          <$> (PatCtor <$> toQualId (ID "left") <*> sequenceA [toId e])
          <*> pure innerMatch
        , Equation
          <$> (PatCtor <$> toQualId (ID "right") <*> sequenceA [toId n])
          <*> pure recursiveCall
        ]

  body    <-
    TermMatch
    <$> (MatchItem
         <$> toRef k
         <*> pure Nothing
         <*> pure Nothing)
    <*> pure Nothing
    <*> sequenceA
        [ Equation
          <$> (PatCtor <$> toQualId h0 <*> pure [])
          <*> pure false
        , Equation
          <$> (PatCtor
               <$> toQualId hs
               <*> sequenceA [toId b, toId k])
          <*> pure namespaceMatch
        ]

  return . SentenceFixpoint $
    Fixpoint [FixpointBody wfindex binders anno (TermSort Prop) body]
