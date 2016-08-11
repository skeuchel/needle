{-# LANGUAGE GADTs #-}

module KnotCore.Elaboration.Lemma.StabilitySubst where

import Control.Applicative

import Coq.StdLib as Coq
import Coq.Syntax as Coq

import KnotCore.Syntax
import KnotCore.Elaboration.Core

lemmas :: Elab m => [FunGroupDecl] -> m Coq.Sentences
lemmas fgds = concat <$> traverse funGroupDecl fgds

funGroupDecl :: Elab m => FunGroupDecl -> m Coq.Sentences
funGroupDecl fgd = do
  deps <- getSortNamespaceDependencies (fst . head $ fgdFuns fgd)
  concat <$> sequenceA
    [ do
        glem  <- groupLemma ntn fgd
        let fns = [ fdName fd | (_,fds) <- fgdFuns fgd, fd <- fds ]
        ilems <- case fns of
                   [_] -> return []
                   _   -> traverse (individualLemma ntn (fgdName fgd)) fns
        return (glem:ilems)
    | ntn <- deps
    ]

individualLemma :: Elab m => NamespaceTypeName -> FunGroupName -> FunName -> m Coq.Sentence
individualLemma ntn fgn fn = do

  (stn,_ntns) <- lookupFunctionType fn
  glem  <- idLemmaStabilitySubstGroup ntn fgn
  lem   <- idLemmaStabilitySubst ntn fn
  sv    <- freshSortVariable stn
  ass   <- individualAssertion ntn sv fn
  proof <- sequenceA
           [ pure (Coq.PrIntros [])
           , Coq.PrTactic "eapply" <$> sequenceA [toRef glem]
           ]
  svbinder <- toBinder sv
  return $ Coq.SentenceAssertionProof
                     (Coq.Assertion Coq.AssLemma lem [svbinder] ass)
                     (Coq.ProofQed [Coq.PrSeq proof])

groupLemma :: Elab m => NamespaceTypeName -> FunGroupDecl -> m Coq.Sentence
groupLemma ntn fgd = do

  let fgn  = fgdName fgd
      sgtn = groupName [ stn | (stn,_) <- fgdFuns fgd ]

  shiftFuns  <- idLemmaStabilitySubstGroup ntn fgn
  induction  <- idFunctionInductionSortGroup fgn sgtn
  assertion <- Coq.all <$>
                  sequenceA
                    [ groupAssertion ntn stn fds
                    | (stn,fds) <- fgdFuns fgd
                    ]
  proof <- sequenceA
           [ Coq.PrTactic "apply_mutual_ind" <$> sequenceA [toRef induction]
           , pure Coq.PrSimpl
           , pure (Coq.PrIntros [])
           , pure (Coq.PrTactic "congruence" [])
           ]

  return $ Coq.SentenceAssertionProof
                     (Coq.Assertion Coq.AssLemma shiftFuns [] assertion)
                     (Coq.ProofQed [Coq.PrSeq proof])


groupAssertion :: Elab m => NamespaceTypeName -> SortTypeName -> [FunDecl] -> m Coq.Term
groupAssertion ntn stn fds = do

  sv <- freshSortVariable stn
  assertions <- Coq.all <$> sequenceA
                  [ individualAssertion ntn sv (fdName fd)
                  | fd <- fds
                  ]

  Coq.TermForall
    <$> sequenceA [toBinder sv]
    <*> pure assertions

individualAssertion :: Elab m => NamespaceTypeName -> SortVariable -> FunName -> m Coq.Term
individualAssertion ntn sv fn = do

  let stn = typeNameOf sv
  subst <- idFunctionSubst ntn stn
  (subStn,_) <- getNamespaceCtor ntn

  xa    <- freshTraceVar ntn
  ta    <- freshSortVariable subStn

  left  <- Coq.TermApp
             <$> toRef fn
             <*> sequenceA
                 [Coq.TermApp
                  <$> toRef subst
                  <*> sequenceA [toRef xa, toRef ta, toRef sv]]

  right <- Coq.TermApp <$> toRef fn <*> sequenceA [toRef sv]

  Coq.TermForall
    <$> sequenceA [toBinder xa, toBinder ta]
    <*> pure (Coq.eq left right)
