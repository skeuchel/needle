
module KnotCore.Elaboration.Weaken where

import Control.Applicative
import Coq.Syntax

import KnotCore.Syntax

import KnotCore.Elaboration.Monad
import KnotCore.Elaboration.Weaken.WeakenTerm

eWeaken :: Elab m => TermSpec -> m Sentences
eWeaken ts = traverse (eFunctionWeakenTerm . sdTypeName) sds
  where sds = tsSortGroupDecls ts >>= sgSorts
