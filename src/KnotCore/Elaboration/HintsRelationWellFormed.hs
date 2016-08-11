{-# LANGUAGE DataKinds #-}

module KnotCore.Elaboration.HintsRelationWellFormed where

import           Coq.StdLib
import           Coq.Syntax

import           KnotCore.DeBruijn.Core
import           KnotCore.Elaboration.Core
import           KnotCore.Elaboration.Eq
import           KnotCore.Syntax

import           Control.Applicative
import           Control.Arrow
import           Control.Monad ((>=>))
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Maybe (catMaybes, mapMaybe)
import           Data.Traversable (for, traverse, sequenceA)

hints :: Elab m => [RelationGroupDecl] -> m [Sentence]
hints rgds = concat <$> traverse eRelationGroupDecl rgds

eRelationGroupDecl :: Elab m => RelationGroupDecl -> m [Sentence]
eRelationGroupDecl (RelationGroupDecl mbEtn rds)
  | Just _ <- mbEtn
  = traverse eRelationDecl rds
  | Nothing <- mbEtn
  = pure []

eRelationDecl :: Elab m => RelationDecl -> m Sentence
eRelationDecl (RelationDecl Nothing _ _ _ _ _) =
  error "KnotCore.Elaboration.Lemma.eRelationDecl: impossible"
eRelationDecl (RelationDecl (Just _ev) rtn fds _roots outputs _rules) = do
  fs <- eFieldDeclFields fds
  h  <- freshVariable "H" Coq.StdLib.true
  hId <- toId h

  proofSteps <-
    for (zip fds [0..]) $ \(fd,i) -> case fd of
      FieldDeclSort _bs _sv _svWf ->
        PrPoseProof
        <$> (TermApp
             <$> (idLemmaRelationWellFormed rtn i >>= toRef)
             <*> sequence
                 (concat
                  [ [pure TermUnderscore]
                  , map (const (pure TermUnderscore)) fs
                  , map (const (pure TermUnderscore)) outputs
                  , [toRef h]
                  ]
                 )
            )
  let proof = PrSeq (proofSteps ++ [PrClear [hId]])

  hyp <- ContextHyp
         <$> toId h
         <*> (PatCtorEx
              <$> toQualId rtn
              <*> sequenceA
                  (concat
                   [ [pure PatUnderscore]
                   , map (const (pure PatUnderscore)) fs
                   , map (const (pure PatUnderscore)) outputs
                   ]
                  )
             )

  pure $!
    SentenceHint ModNone
      (HintExtern 8 Nothing
        (PrMatchGoal
         [ContextRule [hyp] PatUnderscore proof]
        )
      )
      [ID "wf"]


{-
eSortDecl :: Elab m => SortDecl -> m Sentence
eSortDecl (SortDecl stn _ ctors) = localNames $ do

  qid   <- idRelationWellFormed stn >>= toQualId
  rules <- traverse (eCtorDecl qid) ctors


eCtorDecl :: Elab m => QualId -> CtorDecl -> m ContextRule
eCtorDecl wf (CtorVar cn _ _) = localNames $ do

  h     <- freshVariable "H" Coq.StdLib.true >>= toId

  hyp <- ContextHyp h
         <$> (PatCtorEx wf
              <$> sequenceA
                  [ pure PatUnderscore
                  , PatCtor
                    <$> toQualId cn
                    <*> pure [ ID "_" ]
                  ]
             )

  return $ ContextRule [hyp] PatUnderscore
             (PrSeq [PrInversion h, PrSubst, PrClear [h]])
eCtorDecl wf (CtorReg cn fields) = localNames $ do

  hyp <- ContextHyp h
         <$> (PatCtorEx wf
              <$> sequenceA
                  [ pure PatUnderscore
                  , PatCtor
                    <$> toQualId cn
                    <*> pure [ ID "_" | FieldDeclSort{} <- fields ]
                  ]
             )

  return $ ContextRule [hyp] PatUnderscore
             (PrSeq [PrInversion h, PrSubst, PrClear [h]])


Hint Extern 8 (wfTy _ _) =>
  match goal with
    | H: Sub _ _ _ |- _ =>
      pose proof (Sub_wf_0 _ _ _ H);
      pose proof (Sub_wf_1 _ _ _ H);
      clear H
    | H: Typing _ _ _ |- _ =>
      pose proof (Typing_wf_1 _ _ _ H);
      clear H
  end : infra shift wf.
-}
