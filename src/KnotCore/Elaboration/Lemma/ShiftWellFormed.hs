{-# LANGUAGE GADTs #-}

module KnotCore.Elaboration.Lemma.ShiftWellFormed where

import Control.Applicative
import Control.Monad
import Data.Maybe

import Coq.Syntax
import Coq.StdLib

import KnotCore.Syntax
import KnotCore.Elaboration.Core
import KnotCore.Elaboration.Eq

lemmas :: Elab m => [SortGroupDecl] -> m [Sentence]
lemmas sdgs = do
  ntns <- getNamespaces
  concat <$> sequenceA
    [ sortGroupDecl ntn sdg
    | sdg <- sdgs, ntn <- ntns
    ]

sortGroupDecl :: Elab m => NamespaceTypeName -> SortGroupDecl -> m [Sentence]
sortGroupDecl ntn (SortGroupDecl sgtn sds _ hasBs) = localNames $ do

  groupLemma <- idGroupLemmaShiftWellFormedSort ntn sgtn
  h1         <- freshHVarlistVar
  induction  <- idInductionWellFormedSortGroup sgtn

  assertions <- for sds (localNames . sortAssertion h1 ntn . typeNameOf)
  proofs     <- concat <$> traverse (sortProof (map typeNameOf sds) hasBs h1 ntn) sds

  bindh1     <- toBinder h1
  refh1      <- toRef h1

  definition <-
      Definition
      <$> toId groupLemma
      <*> pure []
      <*> pure
            (Just
               (TermForall
                  [bindh1]
                  (TermAnd
                     [ TermForall binders assert
                     | (binders,assert) <- assertions
                     ]
                  )
               )
            )
      <*> (if hasBs
           then TermApp
                <$> toRef induction
                <*> pure
                    ([ TermAbs (bindh1:binders) assert
                     | (binders,assert) <- assertions
                     ] ++ proofs
                    )
           else TermAbs [bindh1]
                <$> (TermApp
                     <$> toRef induction
                     <*> pure
                         (refh1:
                          [ TermAbs binders assert
                          | (binders,assert) <- assertions
                          ] ++ proofs
                         )
                    )
          )

  individual <-
    case sds of
      [_] -> return []
      _   -> for sds $ \sd -> do
               lemma            <- idLemmaShiftWellFormedSort ntn (typeNameOf sd)
               groupLemmaRef    <- toRef groupLemma
               (binders,assert) <- sortAssertion h1 ntn (typeNameOf sd)
               let proof =
                     ProofQed
                       [ PrPoseProof (TermApp groupLemmaRef [refh1]),
                         PrTactic "destruct_conjs" [],
                         PrTactic "easy" []
                       ]
               return (SentenceAssertionProof
                         (Assertion AssLemma lemma [bindh1] (TermForall binders assert))
                         proof)

  return $ SentenceDefinition definition : individual

sortAssertion :: Elab m => HVarlistVar -> NamespaceTypeName -> SortTypeName -> m ([Binder],Term)
sortAssertion h1 ntn stn = do

  t    <- freshSortVariable stn
  wft  <- freshVariable "wf" =<<
          toTerm (WfSort (HVVar h1) (SVar t))
  c    <- freshCutoffVar ntn
  h2   <- freshHVarlistVar

  binders <-
    sequenceA
    [ toBinder t
    , toBinder wft
    ]
  assert <-
    TermForall
    <$> sequenceA
        [ toBinder c
        , toBinder h2
        ]
    <*> (TermFunction
         <$> toTerm (HVarlistInsertion (CVar c) (HVVar h1) (HVVar h2))
         <*> toTerm (WfSort (HVVar h2) (SShift' (CVar c) (SVar t)))
        )
  return (binders,assert)

sortProof :: Elab m => [SortTypeName] -> Bool -> HVarlistVar -> NamespaceTypeName -> SortDecl -> m [Term]
sortProof stns hasBs h1 ntn = traverse (ctorProof stns hasBs h1 ntn) . sdCtors

ctorProof :: Elab m => [SortTypeName] -> Bool -> HVarlistVar -> NamespaceTypeName -> CtorDecl -> m Term
ctorProof stns hasBs h1 ntn cd = localNames $ do

  c    <- freshCutoffVar ntn
  h2   <- freshHVarlistVar
  ins  <- freshVariable "ins" =<<
          toTerm (HVarlistInsertion (CVar c) (HVVar h1) (HVVar h2))

  case cd of
    CtorVar cn mv _ -> do
      -- TOneverDO: use cached names
      i    <- freshIndexVar (typeNameOf mv)
      wfi  <- freshVariable "wfi" =<<
              toTerm (WfIndex (HVVar h1) (IVar i))

      TermAbs
        <$> sequenceA
            ( [ toBinder h1 | hasBs ] ++
              [ toBinder i
              , toBinder wfi
              , toBinder c
              , toBinder h2
              , toBinder ins
              ]
            )
        <*> (TermApp
             <$> (idRelationWellFormedCtor cn >>= toRef)
             <*> sequenceA
                 [ toRef h2
                 , pure TermUnderscore
                 , TermApp
                   <$> (idLemmaShiftWellFormedIndex ntn (typeNameOf mv) >>= toRef)
                   <*> sequenceA
                       [ toRef c
                       , toRef h1
                       , toRef h2
                       , toRef ins
                       , toRef i
                       , toRef wfi
                       ]
                 ]
            )

    CtorReg cn fds -> do

      (binderss,proofs) <-
        unzip . catMaybes
        <$> for fds (\fd ->
               case fd of
                 FieldDeclReference _fv _wfFv ->
                   error "KnotCore.Elaboration.Lemma.ShiftWellFormed.ctorProof.FieldDeclReference: NOT IMPLEMENTED"
                 FieldDeclBinding _bs _bv -> return Nothing
                 FieldDeclSort bs sv _svWf
                   | typeNameOf sv `elem` stns -> do
                       let ebs = simplifyHvl $ evalBindSpec HV0 bs

                       -- TOneverDO: use cached name
                       wf      <- freshVariable "wf" =<<
                                  toTerm (WfSort (simplifyHvlAppend (HVVar h1) ebs) (SVar sv))
                       ih      <- freshInductionHypothesis sv
                       binders <- sequenceA [ toBinder sv, toBinder wf, toBinder ih ]
                       proof   <- TermApp
                                  <$> toRef ih
                                  <*> sequenceA
                                      [ toTerm (simplifyCutoffWeaken (CVar c) ebs)
                                      , toTerm (simplifyHvlAppend (HVVar h2) ebs)
                                      , TermApp
                                        <$> (idLemmaWeakenRelationHVarlistInsert ntn >>= toRef)
                                        <*> sequenceA
                                            [ toTerm ebs
                                            , toRef ins
                                            ]
                                      ]
                       shiftbs <- EqhCongAppend (EqhRefl HV0) <$> eqhvlEvalBindspecShift ntn bs
                       proof' <- case eqhSimplify (EqhCongAppend (EqhRefl (HVVar h2)) (EqhSym shiftbs)) of
                                   EqhRefl _ -> pure proof
                                   eq        -> TermApp (termIdent "eq_ind2")
                                                <$> sequenceA
                                                    [ idRelationWellFormed (typeNameOf sv) >>= toRef
                                                    , toTerm eq
                                                    , toTerm (EqtRefl (typeNameOf sv))
                                                    , pure proof
                                                    ]
                       return $ Just (binders, proof')

                   | otherwise -> do
                       let ebs = simplifyHvl $ evalBindSpec HV0 bs

                       wf      <- freshVariable "wf" =<<
                                  toTerm (WfSort (simplifyHvlAppend (HVVar h1) ebs) (SVar sv))
                       binders <- sequenceA [ toBinder sv, toBinder wf ]
                       proof   <- TermApp
                                  <$> (idLemmaShiftWellFormedSort ntn (typeNameOf sv) >>= toRef)
                                  <*> sequenceA
                                      [ toTerm (simplifyHvlAppend (HVVar h1) ebs)
                                      , toRef sv
                                      , toRef wf
                                      , toTerm (simplifyCutoffWeaken (CVar c) ebs)
                                      , toTerm (simplifyHvlAppend (HVVar h2) ebs)
                                      , TermApp
                                        <$> (idLemmaWeakenRelationHVarlistInsert ntn >>= toRef)
                                        <*> sequenceA
                                            [ toTerm ebs
                                            , toRef ins
                                            ]
                                      ]

                       return $ Just (binders, proof))

      bindh1   <- toBinder h1
      bindc    <- toBinder c
      bindh2   <- toBinder h2
      bindins  <- toBinder ins
      refh2    <- toRef h2

      let binders = concat
                      [ [bindh1 | hasBs ]
                      , concat binderss
                      , [bindc, bindh2, bindins]
                      ]

      TermAbs
        <$> pure binders
        <*> (TermApp
             <$> (idRelationWellFormedCtor cn >>= toRef)
             <*> pure (refh2 : proofs)
            )
