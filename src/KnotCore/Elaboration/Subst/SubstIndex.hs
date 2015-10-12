
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
    s          <- freshSubtreeVar stn
    y          <- freshIndexVar ntn

    eq_x0 <-
      Equation
      <$> (PatCtor <$> toQualId x0 <*> sequence [])
      <*> (TermMatch
           <$> (MatchItem <$> toRef y <*> pure Nothing <*> pure Nothing)
           <*> pure Nothing
           <*> sequence
               [ Equation
                 <$> (PatCtor <$> toQualId i0 <*> sequence [])
                 <*> toRef s,
                 Equation
                 <$> (PatCtor <$> toQualId is <*> sequence [toId y])
                 <*> (TermApp <$> toRef cn <*> sequence [toRef y])
               ]
          )
    rec       <-
      TermApp
      <$> toRef substIndex
      <*> sequence [toRef x, toRef s, toRef y]

    eq_xs <- forM ntns $ \ntn' ->
      Equation
      <$> (PatCtor <$> toQualId xs <*> sequence [toId ntn', toId x])
      <*> (case () of
             _ | ntn' == ntn ->
                   TermMatch
                   <$> (MatchItem <$> toRef y <*> pure Nothing <*> pure Nothing)
                   <*> pure Nothing
                   <*> sequence
                       [ Equation
                         <$> (PatCtor <$> toQualId i0 <*> sequence [])
                         <*> (TermApp <$> toRef cn <*> sequence [toRef i0]),
                         Equation
                         <$> (PatCtor <$> toQualId is <*> sequence [toId y])
                         <*> (TermApp
                              <$> (idFunctionShift ntn' stn >>= toRef)
                              <*> sequence [ toRef c0, pure rec ]
                             )
                       ]
               | ntn' `elem` deps ->
                   TermApp
                   <$> (idFunctionShift ntn' stn >>= toRef)
                   <*> sequence [ toRef c0, pure rec ]
               | otherwise -> pure rec)

    body <-
      FixpointBody
      <$> toId substIndex
      <*> sequence [toBinder x, toBinder s, toBinder y]
      <*> (Just . Struct <$> toId x)
      <*> toRef stn
      <*> (TermMatch
           <$> (MatchItem <$> toRef x <*> pure Nothing <*> pure Nothing)
           <*> pure Nothing
           <*> pure (eq_x0 : eq_xs)
          )

    return $ SentenceFixpoint (Fixpoint [body])
