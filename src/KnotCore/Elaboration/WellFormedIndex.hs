
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
               <*> sequence [toRef a]

  k         <- freshHVarlistVar
  h0        <- idCtorHVarlistNil
  hs        <- idCtorHVarlistCons

  i0        <- idFamilyIndexZero
  is        <- idFamilyIndexSucc
  i         <- freshVariable "i" indexa

  eq_ab     <- eq <$> toRef a <*> toRef b
  e         <- freshVariable "e" eq_ab
  n         <- freshVariable "n" (Coq.StdLib.not eq_ab)

  binders <- sequence [toImplicitBinder a, toBinder k, toBinder i]
  anno    <- Just . Struct <$> toId k

  rec     <- TermApp
             <$> toRef wfindex
             <*> sequence [toRef k, toRef i]

  innerMatch <-
    TermMatch
    <$> (MatchItem
         <$> toRef i
         <*> pure Nothing
         <*> pure Nothing
        )
    <*> pure Nothing
    <*> sequence
        [ Equation
          <$> (PatCtor <$> toQualId i0 <*> pure [])
          <*> pure true
        , Equation
          <$> (PatCtor <$> toQualId is <*> sequence [toId i])
          <*> pure rec
        ]

  namespaceMatch <-
    TermMatch
    <$> (MatchItem
         <$> (TermApp
              <$> (idLemmaEqNamespaceDec >>= toRef)
              <*> sequence [ toRef a, toRef b ]
             )
         <*> pure Nothing
         <*> pure Nothing
        )
    <*> pure Nothing
    <*> sequence
        [ Equation
          <$> (PatCtor <$> toQualId (ID "left") <*> sequence [toId e])
          <*> pure innerMatch
        , Equation
          <$> (PatCtor <$> toQualId (ID "right") <*> sequence [toId n])
          <*> pure rec
        ]

  body    <-
    TermMatch
    <$> (MatchItem
         <$> toRef k
         <*> pure Nothing
         <*> pure Nothing)
    <*> pure Nothing
    <*> sequence
        [ Equation
          <$> (PatCtor <$> toQualId h0 <*> pure [])
          <*> pure false
        , Equation
          <$> (PatCtor
               <$> toQualId hs
               <*> sequence [toId b, toId k])
          <*> pure namespaceMatch
        ]

  return . SentenceFixpoint $ Fixpoint [FixpointBody wfindex binders anno (TermSort Prop) body]
