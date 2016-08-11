
module KnotCore.Elaboration.Weaken.Class where

import Control.Applicative

import Coq.StdLib
import Coq.Syntax

import KnotCore.Elaboration.Core

eWeakenClass :: Elab m => m [Sentence]
eWeakenClass = localNames $
  do
    setA <- freshVariable "A" (TermSort Type)
    a1   <- freshVariable "a" =<< toRef setA
    a2   <- freshVariable "a" =<< toRef setA
    k1   <- freshHVarlistVar
    k2   <- freshHVarlistVar
    append       <- idAppendHVarlist
    weaken       <- idMethodWeaken
    weakenInj    <- idMethodWeakenInj
    weakenAppend <- idMethodWeakenAppend

    declWeaken    <-
      MethodDeclaration weaken
      <$> sequenceA [toBinder a1, toBinder k1]
      <*> toRef setA

    declWeakenInj <-
      MethodDeclaration weakenInj
      <$> sequenceA [toBinder k1, toBinder a1, toBinder a2]
      <*> (TermFunction
           <$> (eq
                <$> (TermApp
                     <$> toRef weaken
                     <*> sequenceA [toRef a1,toRef k1]
                    )
                <*> (TermApp
                     <$> toRef weaken
                     <*> sequenceA [toRef a2,toRef k1]
                    )
               )
           <*> (eq
                <$> toRef a1
                <*> toRef a2
               )
          )

    declWeakenAppend <-
      MethodDeclaration weakenAppend
      <$> sequenceA [toBinder a1, toBinder k1, toBinder k2]
      <*> (eq
           <$> (TermApp
                <$> toRef weaken
                <*> sequenceA
                    [TermApp
                     <$> toRef weaken
                     <*> sequenceA [toRef a1, toRef k1],
                     toRef k2
                    ]
               )
           <*> (TermApp
                <$> toRef weaken
                <*> sequenceA
                    [toRef a1,
                     TermApp
                     <$> toRef append
                     <*> sequenceA [toRef k1, toRef k2]
                    ]
               )
          )

    classDecl <-
      ClassDeclaration
      <$> idClassWeaken
      <*> sequenceA [toBinder setA]
      <*> pure (Just Type)
      <*> pure [declWeaken, {- declWeakenInj, -} declWeakenAppend ]

    return [SentenceClassDecl classDecl]
