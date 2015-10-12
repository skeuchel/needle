
module KnotCore.Elaboration.Subst where

import Control.Applicative
import Coq.Syntax

import KnotCore.Syntax

import KnotCore.Elaboration.Monad
import KnotCore.Elaboration.Subst.SubstIndex
import KnotCore.Elaboration.Subst.SubstTerm

eSubst :: Elab m => TermSpec -> m Sentences
eSubst ts =
  concat <$> sequence
    [ mapM eSubstIndex (tsNamespaceDecls ts),
      eSortGroupDecls (tsSortGroupDecls ts)
    ]
