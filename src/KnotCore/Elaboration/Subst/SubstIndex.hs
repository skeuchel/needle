{-# LANGUAGE GADTs #-}

module KnotCore.Elaboration.Subst.SubstIndex where

import Control.Applicative
import Control.Monad

import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core

eSubstIndex :: Elab m => NamespaceDecl -> m Sentence
eSubstIndex nd = localNames $
  do
    let ntn = typeNameOf nd
    (stn,cn)   <- getNamespaceCtor ntn
    deps       <- getSortNamespaceDependencies stn
    ntns       <- getNamespaces

    x0         <- idFamilyTraceNil
    xs         <- idFamilyTraceCons
    c0         <- idFamilyCutoffZero
    i0         <- idFamilyIndexZero
    is         <- idFamilyIndexSucc

    substIndex <- idFunctionSubstIndex ntn
    x          <- freshTraceVar ntn
    s          <- freshSortVariable stn
    y          <- freshIndexVar ntn

    eq_x0 <-
      Equation
      <$> (PatCtor <$> toQualId x0 <*> sequenceA [])
      <*> (TermMatch
           <$> (MatchItem <$> toRef y <*> pure Nothing <*> pure Nothing)
           <*> pure Nothing
           <*> sequenceA
               [ Equation
                 <$> (PatCtor <$> toQualId i0 <*> sequenceA [])
                 <*> toRef s,
                 Equation
                 <$> (PatCtor <$> toQualId is <*> sequenceA [toId y])
                 <*> (TermApp <$> toRef cn <*> sequenceA [toRef y])
               ]
          )
    recursiveCall <-
      TermApp
      <$> toRef substIndex
      <*> sequenceA [toRef x, toRef s, toRef y]

    eq_xs <- for ntns $ \ntn' ->
      Equation
      <$> (PatCtor <$> toQualId xs <*> sequenceA [toId ntn', toId x])
      <*> (case () of
             _ | ntn' == ntn ->
                   TermMatch
                   <$> (MatchItem <$> toRef y <*> pure Nothing <*> pure Nothing)
                   <*> pure Nothing
                   <*> sequenceA
                       [ Equation
                         <$> (PatCtor <$> toQualId i0 <*> sequenceA [])
                         <*> (TermApp <$> toRef cn <*> sequenceA [toRef i0]),
                         Equation
                         <$> (PatCtor <$> toQualId is <*> sequenceA [toId y])
                         <*> (TermApp
                              <$> (idFunctionShift ntn' stn >>= toRef)
                              <*> sequenceA [ toRef c0, pure recursiveCall ]
                             )
                       ]
               | ntn' `elem` deps ->
                   TermApp
                   <$> (idFunctionShift ntn' stn >>= toRef)
                   <*> sequenceA [ toRef c0, pure recursiveCall ]
               | otherwise -> pure recursiveCall)

    body <-
      FixpointBody
      <$> toId substIndex
      <*> sequenceA [toBinder x, toBinder s, toBinder y]
      <*> (Just . Struct <$> toId x)
      <*> toRef stn
      <*> (TermMatch
           <$> (MatchItem <$> toRef x <*> pure Nothing <*> pure Nothing)
           <*> pure Nothing
           <*> pure (eq_x0 : eq_xs)
          )

    return $ SentenceFixpoint (Fixpoint [body])
