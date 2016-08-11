{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}

module KnotSpec.Desugar (desugar) where


import           KnotSpec.Syntax
import           KnotSpec.Environment
import           KnotSpec.DesugarRelations
import           KnotSpec.DesugarSorts

import qualified KnotCore.Syntax as Core

import           Control.Monad.Error.Class
import qualified Data.Map as M
import           Data.Maybe
import           Data.Traversable

--------------------------------------------------------------------------------

desugar :: (MonadError String m, EnvM m, FreshM m) =>
  TermSpec 'Grouped -> m Core.TermSpec
desugar (TermSpecGrouped nds sgds eds fgds rgds zgds) = do
  let sds        = concatMap sgdSorts sgds
  Core.TermSpec
    <$> traverse (namespaceDecl (mkMECtorVars SGrouped sds)) nds
    <*> pure (functionEnv (concatMap snd $ concatMap fgdFunDecls fgds))
    <*> traverse sortGroupDecl sgds
    <*> traverse funGroupDecl fgds
    <*> traverse (envDecl (concatMap rgdRelations rgds)) eds
    <*> traverse relationGroupDecl rgds
    <*> traverse setGroupDecl zgds
    <*> pure (makeSubstitutableClauses eds (concatMap rgdRelations rgds))

functionEnv :: [FunDecl 'Grouped] -> Core.FunctionEnv
functionEnv  fds =
  M.fromListWith (M.unionWith (error "functionEnv"))
    [ (stn, M.singleton fn ntns)
    | (fn,(stn,ntns)) <-
        [ (fdName fd, (fdSource fd, fdTarget fd))
        | fd <- fds
        ]
    ]
