
module KnotCore.Elaboration.HVarlist where

import Control.Applicative

import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core

eHVarlist :: Elab m => m [Sentence]
eHVarlist =
  sequence
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

  SentenceInductive . Inductive <$> sequence
    [ InductiveBody
      <$> toId hvl
      <*> pure []
      <*> pure (TermSort Type)
      <*> sequence
          [ InductiveCtor
            <$> toId nil
            <*> pure []
            <*> pure Nothing,
            InductiveCtor
            <$> toId cons
            <*> sequence [toBinder a, toBinder k]
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

  SentenceFixpoint . Fixpoint <$> sequence
    [ FixpointBody
      <$> toId append
      <*> sequence [toBinder k1, toBinder k2]
      <*> (Just . Struct <$> toId k2)
      <*> toRef hvl
      <*> (TermMatch
           <$> (MatchItem
                <$> toRef k2
                <*> pure Nothing
                <*> pure Nothing)
           <*> pure Nothing
           <*> sequence
               [ Equation
                 <$> (PatCtor <$> toQualId nil <*> pure [])
                 <*> toRef k1,
                 Equation
                 <$> (PatCtor
                      <$> toQualId cons
                      <*> sequence [toId a, toId k2])
                 <*> (TermApp
                      <$> toRef cons
                      <*> sequence
                          [ toRef a,
                            TermApp
                            <$> toRef append
                            <*> sequence [toRef k1, toRef k2]
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
    <$> sequence [toBinder h0, toBinder h1, toBinder h2]
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
