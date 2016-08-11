
module KnotCore.Elaboration.HVarlist where

import Control.Applicative

import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core

eHVarlist :: Elab m => m [Sentence]
eHVarlist =
  sequenceA
  [ eTypeHVarlist
  , pure SentenceBlankline
  , eFunctionAppendHVarlist
  , pure SentenceBlankline
  , eLemmaHVarlistAppendAssoc
  -- , pure SentenceBlankline
  -- , eTacticSpecializeNil
  ]

eTypeHVarlist :: Elab m => m Sentence
eTypeHVarlist = localNames $ do

  namespace <- idTypeNamespace
  a         <- freshVariable "a" =<< toRef namespace
  hvl       <- idTypeHVarlist
  nil       <- idCtorHVarlistNil
  cons      <- idCtorHVarlistCons

  k         <- freshHVarlistVar

  SentenceInductive . Inductive <$> sequenceA
    [ InductiveBody
      <$> toId hvl
      <*> pure []
      <*> pure (TermSort Type)
      <*> sequenceA
          [ InductiveCtor
            <$> toId nil
            <*> pure []
            <*> pure Nothing,
            InductiveCtor
            <$> toId cons
            <*> sequenceA [toBinder a, toBinder k]
            <*> pure Nothing
          ]
    ]

eFunctionAppendHVarlist :: Elab m => m Sentence
eFunctionAppendHVarlist = localNames $ do

  namespace <- idTypeNamespace
  a         <- freshVariable "a" =<< toRef namespace
  hvl       <- idTypeHVarlist
  nil       <- idCtorHVarlistNil
  cons      <- idCtorHVarlistCons
  append    <- idAppendHVarlist

  k1        <- freshHVarlistVar
  k2        <- freshHVarlistVar

  SentenceFixpoint . Fixpoint <$> sequenceA
    [ FixpointBody
      <$> toId append
      <*> sequenceA [toBinder k1, toBinder k2]
      <*> (Just . Struct <$> toId k2)
      <*> toRef hvl
      <*> (TermMatch
           <$> (MatchItem
                <$> toRef k2
                <*> pure Nothing
                <*> pure Nothing)
           <*> pure Nothing
           <*> sequenceA
               [ Equation
                 <$> (PatCtor <$> toQualId nil <*> pure [])
                 <*> toRef k1,
                 Equation
                 <$> (PatCtor
                      <$> toQualId cons
                      <*> sequenceA [toId a, toId k2])
                 <*> (TermApp
                      <$> toRef cons
                      <*> sequenceA
                          [ toRef a,
                            TermApp
                            <$> toRef append
                            <*> sequenceA [toRef k1, toRef k2]
                          ]
                     )
               ]
          )
    ]

eLemmaHVarlistAppendAssoc :: Elab m => m Sentence
eLemmaHVarlistAppendAssoc = localNames $ do

  lemma      <- idLemmaHVarlistAppendAssoc

  h0         <- freshHVarlistVar
  h1         <- freshHVarlistVar
  h2         <- freshHVarlistVar

  statement  <-
    TermForall
    <$> sequenceA [toBinder h0, toBinder h1, toBinder h2]
    <*> (TermEq
         <$> toTerm (HVAppend (HVAppend (HVVar h0) (HVVar h1)) (HVVar h2))
         <*> toTerm (HVAppend (HVVar h0) (HVAppend (HVVar h1) (HVVar h2)))
        )

  let assertion :: Assertion
      assertion = Assertion AssLemma lemma [] statement

      proof :: Proof
      proof = ProofQed [PrTactic "needleGenericWeakenAppend" []]

  return $ SentenceAssertionProof assertion proof

eTacticSpecializeNil :: Elab m => m Sentence
eTacticSpecializeNil = do
  ID spec <- idTacticSpecializeHVarlistNil
  ID hvl  <- idTypeHVarlist
  ID nil  <- idCtorHVarlistNil

  return . SentenceVerbatim $
    "Ltac " ++ spec ++ " :=\n" ++
    "  progress\n" ++
    "    repeat\n" ++
    "    match goal with\n" ++
    "      | [ H : (forall _ : ?P, _), x : ?P |- _ ] => specialize (H x)\n" ++
    "      | [ H : (forall _ : " ++ hvl ++ ", _) |- _ ] => specialize (H " ++ nil ++ ")\n" ++
    "    end."
