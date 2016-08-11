
module KnotCore.Elaboration.WeakenTrace where

import Control.Applicative

import Coq.Syntax

import KnotCore.Elaboration.Core

eWeakenTrace :: Elab m => m [Sentence]
eWeakenTrace = localNames $
  do
    append       <- appendTraceId
    weaken       <- idMethodWeaken
    weakenTrace  <- idInstanceWeakenTrace
    trace        <- typeTraceId

    methodWeaken <-
      Method
      <$> toId weaken
      <*> pure []
      <*> toRef append

    classInst <-
      ClassInstance weakenTrace
      <$> idClassWeaken
      <*> sequenceA [toRef trace]
      <*> pure [methodWeaken]

    return [SentenceClassInst classInst]
