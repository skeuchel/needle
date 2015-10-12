
module KnotCore.Elaboration.HVarlistInsertion where

import Control.Applicative
import Control.Monad

import Coq.StdLib
import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core

eHVarlistInsertions :: Elab m => m [Sentence]
eHVarlistInsertions = do
  ntns <- getNamespaces
  concat <$> sequence
    [ mapM eHVarlistInsertion ntns
    , mapM eWeakenHVarlistInsertion ntns
    ]

eHVarlistInsertion :: Elab m => NamespaceTypeName -> m Sentence
eHVarlistInsertion ntn = localNames $ do

  c    <- freshCutoffVar ntn
  h1   <- freshHVarlistVar
  h2   <- freshHVarlistVar

  here <- InductiveCtor
          <$> idRelationHVarlistInsertHere ntn
          <*> sequence [toBinder h1]
          <*> (Just <$> toTerm (HVarlistInsertion (C0 ntn) (HVVar h1) (HVS ntn (HVVar h1))))

  ntns   <- getNamespaces
  theres <- forM ntns $ \tntn ->
              InductiveCtor
              <$> idRelationHVarlistInsertThere ntn tntn
              <*> sequence [toBinder c, toBinder h1, toBinder h2]
              <*> (Just
                   <$> (TermFunction
                        <$> toTerm (HVarlistInsertion (CVar c) (HVVar h1) (HVVar h2))
                        <*> toTerm (HVarlistInsertion
                                     (if ntn == tntn
                                      then CS (CVar c)
                                      else CVar c)
                                     (HVS tntn (HVVar h1))
                                     (HVS tntn (HVVar h2)))
                       )
                  )

  body <- InductiveBody
          <$> idRelationHVarlistInsert ntn
          <*> pure []
          <*> (TermForall
               <$> sequence [ toBinder c, toBinder h1, toBinder h2 ]
               <*> pure (TermSort Prop)
              )
          <*> pure (here:theres)

  return (SentenceInductive $ Inductive [body])

eWeakenHVarlistInsertion :: Elab m => NamespaceTypeName -> m Sentence
eWeakenHVarlistInsertion ntn = localNames $ do

  lemma <- idLemmaWeakenRelationHVarlistInsert ntn
  h     <- freshHVarlistVar
  c     <- freshCutoffVar ntn
  h1    <- freshHVarlistVar
  h2    <- freshHVarlistVar

  statement <- TermForall
               <$> sequence
                   [ toBinder h
                   , toImplicitBinder c
                   , toImplicitBinder h1
                   , toImplicitBinder h2
                   ]
               <*> (TermFunction
                    <$> toTerm (HVarlistInsertion
                                  (CVar c)
                                  (HVVar h1)
                                  (HVVar h2))
                    <*> toTerm (HVarlistInsertion
                                  (CWeaken (CVar c) (HVVar h))
                                  (HVAppend (HVVar h1) (HVVar h))
                                  (HVAppend (HVVar h2) (HVVar h)))
                   )

  let assertion = Assertion AssLemma lemma [] statement
      proof     = ProofQed [PrTactic "needleGenericWeakenHVarlistInsert" []]

  return $ SentenceAssertionProof assertion proof
