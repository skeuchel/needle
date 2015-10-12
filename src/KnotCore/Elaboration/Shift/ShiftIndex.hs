
module KnotCore.Elaboration.Shift.ShiftIndex where

import Control.Applicative

import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core

eShiftIndex :: Elab m => NamespaceDecl -> m Sentence
eShiftIndex nd = localNames $
  do
    let ntn = typeNameOf nd

    shiftIndex <- idFunctionShiftIndex ntn
    cutoff     <- freshCutoffVar ntn
    cId        <- toId cutoff
    cRef       <- toRef cutoff
    cIntro     <- toBinder cutoff
    index      <- freshIndexVar ntn
    xId        <- toId index
    xRef       <- toRef index
    xIntro     <- toBinder index
    idxType    <- typeIndex ntn

    c0 <- idFamilyCutoffZero
    cs <- idFamilyCutoffSucc
    i0 <- idFamilyIndexZero
    is <- idFamilyIndexSucc

    body <- TermMatch
            <$> pure (MatchItem cRef Nothing Nothing)
            <*> pure Nothing
            <*> sequence
                [ Equation
                  <$> (PatCtor <$> toQualId c0 <*> pure [])
                  <*> (TermApp <$> toRef is <*> pure [xRef]),
                  Equation
                  <$> (PatCtor <$> toQualId cs <*> pure [cId])
                  <*> (TermMatch
                       <$> pure (MatchItem xRef Nothing Nothing)
                       <*> pure Nothing
                       <*> sequence
                           [ Equation
                             <$> (PatCtor
                                  <$> toQualId i0
                                  <*> pure [])
                             <*> toRef i0,
                             Equation
                             <$> (PatCtor
                                  <$> toQualId is
                                  <*> pure [xId])
                             <*> (TermApp
                                  <$> toRef is
                                  <*> sequence [TermApp
                                                <$> toRef shiftIndex
                                                <*> pure [cRef, xRef]])
                           ])
                ]

    return . SentenceFixpoint . Fixpoint $
      [ FixpointBody
          shiftIndex
          [cIntro, xIntro]
          (Just $ Struct cId)
          idxType
          body
      ]
