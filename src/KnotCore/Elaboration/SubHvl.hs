module KnotCore.Elaboration.SubHvl where

import Control.Applicative
import Control.Monad
import Data.List (sort)
import Coq.Syntax
import Coq.StdLib

import KnotCore.Syntax
import KnotCore.Elaboration.Core

eSubHvl :: Elab m => [NamespaceTypeName] -> m [Sentence]
eSubHvl ntns = do
  funs <- eFunctionSubHvl ntns
  app  <- eSubHvlAppend ntns
  return $ [funs , app]

eFunctionSubHvl :: Elab m => [NamespaceTypeName] -> m Sentence
eFunctionSubHvl ntns = localNames $ do

  k         <- freshHVarlistVar
  nil       <- idCtorHVarlistNil
  cons      <- idCtorHVarlistCons
  namespace <- idTypeNamespace
  a         <- freshVariable "a" =<< toRef namespace

  subhvl    <- idFunctionSubHvl ntns
  single'    <- hasSingleNamespace
  allNtns   <- getNamespaces
  let single = single' || sort allNtns == ntns
  nmEqs <- forM ntns $ \ntn -> do
             nm        <- idCtorNamespace ntn
             Equation
               <$> (PatCtor <$> toQualId nm <*> pure [])
               <*> (TermApp
                   <$> toRef subhvl
                   <*> sequence [toRef k]
                   )
  nmWl <- Equation
          <$> pure PatUnderscore
          <*> pure (Coq.StdLib.false)

  nmMatch <-
    TermMatch
    <$> (MatchItem <$> toRef a <*> pure Nothing <*> pure Nothing)
    <*> pure Nothing
    <*> pure (if single then nmEqs else nmEqs ++ [nmWl])

  SentenceFixpoint . Fixpoint <$> sequence
    [ FixpointBody
      <$> toId subhvl
      <*> sequence [toBinder k]
      <*> (Just . Struct <$> toId k)
      <*> (pure $ TermSort Prop)
      <*> (TermMatch
           <$> (MatchItem
                <$> toRef k
                <*> pure Nothing
                <*> pure Nothing)
           <*> pure Nothing
           <*> sequence
               [ Equation
                 <$> (PatCtor <$> toQualId nil <*> pure [])
                 <*> pure Coq.StdLib.true
               , Equation
                 <$> (PatCtor
                      <$> toQualId cons
                      <*> sequence [toId a, toId k])
                 <*> pure nmMatch
               ]
          )
    ]

eSubHvlAppend :: Elab m => [NamespaceTypeName] -> m Sentence
eSubHvlAppend ntns = do

  subhvlAppend <- idLemmaSubHvlAppend ntns
  k1           <- freshHVarlistVar
  k2           <- freshHVarlistVar

  assertion <-
    TermForall
    <$> sequence [toBinder k1, toBinder k2]
    <*> (foldr1 TermFunction <$>
         sequence
         [ toTerm (SubHvl ntns (HVVar k1))
         , toTerm (SubHvl ntns (HVVar k2))
         , toTerm (SubHvl ntns (HVAppend (HVVar k1) (HVVar k2)))
         ]
        )

  proof <- sequence
    [ pure $ PrTactic "needleGenericSubHvlAppend" []
    ]

  return $
    SentenceAssertionProof
      (Assertion AssLemma subhvlAppend [] assertion)
      (ProofQed proof)
