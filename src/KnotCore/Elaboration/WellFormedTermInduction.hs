
module KnotCore.Elaboration.WellFormedTermInduction where

import Control.Applicative

import qualified Coq.Syntax as Coq

import KnotCore.Syntax
import KnotCore.Elaboration.Core

eSortGroupDecls :: Elab m => [SortGroupDecl] -> m [Coq.Sentence]
eSortGroupDecls = fmap concat . mapM eSortGroupDecl

eSortGroupDecl :: Elab m => SortGroupDecl -> m [Coq.Sentence]
eSortGroupDecl sg =
  do
    let sgtn = typeNameOf sg
        sds  = sgSorts sg

    individual <- Coq.SentenceScheme . Coq.Scheme
                    <$> mapM eSortDecl sds
    group      <- Coq.SentenceCombinedScheme
                    <$> idInductionWellFormedSortGroup sgtn
                    <*> mapM (idInductionWellFormedSort . typeNameOf) sds
    case sds of
      [_] -> return [individual]
      _   -> return [individual,group]

eSortDecl :: Elab m => SortDecl -> m Coq.SchemeBody
eSortDecl (SortDecl stn _ _) =
  Coq.SchemeInduction
    <$> idInductionWellFormedSort stn
    <*> idRelationWellFormed stn
