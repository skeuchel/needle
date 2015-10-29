
module KnotCore.Elaboration.WellFormedInversion where

import Control.Applicative
import Control.Monad
import Data.Maybe

import Coq.StdLib
import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core
import KnotCore.Elaboration.Eq

eSortGroupDecls :: Elab m => [SortGroupDecl] -> m [Sentence]
eSortGroupDecls sgs = sequence [ eSortDecl sd | sg <- sgs, sd <- sgSorts sg ]

eSortDecl :: Elab m => SortDecl -> m Sentence
eSortDecl (SortDecl stn _ ctors) = localNames $ do

  qid   <- idRelationWellFormed stn >>= toQualId
  rules <- mapM (eCtorDecl qid) ctors

  return $ SentenceHint ModNone
            (HintExtern 2 (Just $ PatCtor qid [ID "_", ID "_"])
               (PrMatchGoal rules))
            [ID "infra", ID "wf"]

eCtorDecl :: Elab m => QualId -> CtorDecl -> m ContextRule
eCtorDecl wf (CtorVar cn _) = localNames $ do

  h     <- freshVariable "H" Coq.StdLib.true >>= toId

  hyp <- ContextHyp h
         <$> (PatCtorEx wf
              <$> sequence
                  [ pure PatUnderscore
                  , PatCtor
                    <$> toQualId cn
                    <*> pure [ ID "_" ]
                  ]
             )

  return $ ContextRule [hyp] PatUnderscore
             (PrSeq [PrInversion h, PrSubst, PrClear [h]])
eCtorDecl wf (CtorTerm cn fields) = localNames $ do
  h     <- freshVariable "H" Coq.StdLib.true >>= toId

  hyp <- ContextHyp h
         <$> (PatCtorEx wf
              <$> sequence
                  [ pure PatUnderscore
                  , PatCtor
                    <$> toQualId cn
                    <*> pure [ ID "_" | FieldSubtree _ _ <- fields ]
                  ]
             )

  return $ ContextRule [hyp] PatUnderscore
             (PrSeq [PrInversion h, PrSubst, PrClear [h]])
