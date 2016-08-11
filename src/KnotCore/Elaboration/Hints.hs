
module KnotCore.Elaboration.Hints where

import qualified Coq.StdLib as Coq
import qualified Coq.Syntax as Coq

import KnotCore.Elaboration.Core
import KnotCore.Elaboration.Monad

mkRewriteHints :: Elab m => [String] -> [Coq.Identifier] -> m [Coq.Sentence]
mkRewriteHints _   []  = return []
mkRewriteHints dbs ids = do
  tms <- traverse toRef ids
  return
    [ Coq.SentenceHint Coq.ModNone (Coq.HintRewrite tms) [Coq.ID db]
    | db <- dbs
    ]

mkRewriteRightToLeftHints :: Elab m => [String] -> [Coq.Identifier] -> m [Coq.Sentence]
mkRewriteRightToLeftHints _   []  = return []
mkRewriteRightToLeftHints dbs ids = do
  tms <- traverse toRef ids
  return
    [ Coq.SentenceHint Coq.ModNone (Coq.HintRewriteRightToLeft tms) [Coq.ID db]
    | db <- dbs
    ]

mkResolveHints :: Elab m => [String] -> [Coq.Identifier] -> m [Coq.Sentence]
mkResolveHints _   []  = return []
mkResolveHints dbs ids = do
  tms <- traverse toRef ids
  return
    [ Coq.SentenceHint Coq.ModNone (Coq.HintResolve tms) [Coq.ID db]
    | db <- dbs
    ]
mkConstructorsHints :: Elab m => [String] -> [Coq.Identifier] -> m [Coq.Sentence]
mkConstructorsHints _   []  = return []
mkConstructorsHints dbs ids =
  return
    [ Coq.SentenceHint Coq.ModNone (Coq.HintConstructors ids) [Coq.ID db]
    | db <- dbs
    ]
