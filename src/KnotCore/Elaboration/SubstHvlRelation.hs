
module KnotCore.Elaboration.SubstHvlRelation where

import Control.Applicative
import Control.Monad

import Coq.StdLib
import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core

eSubstHvlRelations :: Elab m => m [Sentence]
eSubstHvlRelations = do
  ntns <- getNamespaces
  concat <$> sequenceA
    [ traverse eSubstHvlRelation ntns
    , traverse eWeakenSubstHvl ntns
    ]

eSubstHvlRelation :: Elab m => NamespaceTypeName -> m Sentence
eSubstHvlRelation ntn = localNames $ do

  h    <- freshHVarlistVar
  x    <- freshTraceVar ntn
  h1   <- freshHVarlistVar
  h2   <- freshHVarlistVar

  here <- InductiveCtor
          <$> idCtorSubstHvlHere ntn
          <*> pure []
          <*> (Just <$> toTerm (SubstHvl (HVVar h) (T0 ntn) (HVS ntn (HVVar h)) (HVVar h)))

  ntns   <- getNamespaces
  theres <- for ntns $ \tntn ->
              InductiveCtor
              <$> idCtorSubstHvlThere ntn tntn
              <*> sequenceA
                  [ toImplicitBinder x
                  , toImplicitBinder h1
                  , toImplicitBinder h2
                  ]
              <*> (Just
                   <$> (TermFunction
                        <$> toTerm (SubstHvl (HVVar h) (TVar x) (HVVar h1) (HVVar h2))
                        <*> toTerm (SubstHvl
                                     (HVVar h)
                                     (TS tntn (TVar x))
                                     (HVS tntn (HVVar h1))
                                     (HVS tntn (HVVar h2)))
                       )
                  )

  body <- InductiveBody
          <$> idTypeSubstHvl ntn
          <*> sequenceA [toBinder h]
          <*> (TermForall
               <$> sequenceA [toBinder x, toBinder h1, toBinder h2 ]
               <*> pure (TermSort Prop)
              )
          <*> pure (here:theres)

  return (SentenceInductive $ Inductive [body])

eWeakenSubstHvl :: Elab m => NamespaceTypeName -> m Sentence
eWeakenSubstHvl ntn = localNames $ do

  lemma <- idLemmaWeakenSubstHvl ntn
  d     <- freshHVarlistVar
  h     <- freshHVarlistVar
  x     <- freshTraceVar ntn
  h1    <- freshHVarlistVar
  h2    <- freshHVarlistVar

  statement <- TermForall
               <$> sequenceA
                   [ toImplicitBinder h
                   , toBinder d
                   , toImplicitBinder x
                   , toImplicitBinder h1
                   , toImplicitBinder h2
                   ]
               <*> (TermFunction
                    <$> toTerm (SubstHvl
                                  (HVVar h)
                                  (TVar x)
                                  (HVVar h1)
                                  (HVVar h2))
                    <*> toTerm (SubstHvl
                                  (HVVar h)
                                  (TWeaken (TVar x) (HVVar d))
                                  (HVAppend (HVVar h1) (HVVar d))
                                  (HVAppend (HVVar h2) (HVVar d)))
                   )

  let assertion = Assertion AssLemma lemma [] statement
      proof     = ProofQed [PrTactic "needleGenericWeakenSubstHvl" []]

  return $ SentenceAssertionProof assertion proof
