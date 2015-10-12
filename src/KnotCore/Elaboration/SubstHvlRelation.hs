
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
  concat <$> sequence
    [ mapM eSubstHvlRelation ntns
    , mapM eWeakenSubstHvl ntns
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
  theres <- forM ntns $ \tntn ->
              InductiveCtor
              <$> idCtorSubstHvlThere ntn tntn
              <*> sequence
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
          <*> sequence [toBinder h]
          <*> (TermForall
               <$> sequence [toBinder x, toBinder h1, toBinder h2 ]
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
               <$> sequence
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
