{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module KnotSpec.Check (check) where

import           KnotSpec.CheckFuns
import           KnotSpec.CheckRelations
import           KnotSpec.CheckSets
import           KnotSpec.CheckSorts
import           KnotSpec.Evaluation
import           KnotSpec.Syntax

import           Control.Monad.Error.Class

check :: (EnvM m, MonadError String m) =>
  TermSpec 'ResolvedVars -> m (TermSpec 'Checked)
check (TermSpec nds sds eds fnds rds zds) =
  flip runTcT (makeTcEnv sds fnds) $ do
    nds'  <- traverse checkNamespaceDecl nds
    sds'  <- traverse checkSortDecl sds
    eds'  <- traverse checkEnvDecl eds
    fnds' <- traverse checkFunDecl fnds
    zds'  <- traverse checkSetDecl zds
    relTcEnv <- makeRelTcEnv sds' eds' rds
    rds'  <- runEvalT
               (runRelTcT
                  (traverse checkRelationDecl rds)
                  relTcEnv)
               (makeEvalEnv fnds')
    pure (TermSpec nds' sds' eds' fnds' rds' zds')

checkNamespaceDecl :: Applicative m =>
  NamespaceDecl 'ResolvedVars -> m (NamespaceDecl 'Checked)
checkNamespaceDecl (NamespaceDecl beg ntn nrs mbSort dirs end) =
  pure (NamespaceDecl beg ntn nrs mbSort dirs end)
