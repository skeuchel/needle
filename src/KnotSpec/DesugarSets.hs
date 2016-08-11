{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}

module KnotSpec.DesugarSets where

import           Knot.Env
import           Knot.Fresh
import           KnotSpec.Syntax
import           KnotSpec.Environment

import qualified KnotCore.Syntax as Core
import qualified KnotCore.Elaboration.Fresh as Core

import           Control.Monad.Error.Class
import qualified Data.Foldable as F
import           Data.List (intercalate)
import qualified Data.Map as M
import           Data.Monoid ((<>))

envDecl :: DesugarM m => EnvDecl 'Grouped -> m Core.EnvDecl
envDecl (EnvDecl etn nrs ecds) =
  Core.EnvDecl etn nrs <$> traverse envCtorDecl ecds

envCtorDecl :: DesugarM m => EnvCtorDecl 'Grouped -> m Core.EnvCtor
envCtorDecl ecd = case ecd of
  EnvCtorNil cn -> pure (Core.EnvCtorNil cn)
  EnvCtorCons cn bv ecfds ->
    Core.EnvCtorCons cn bv <$>
      traverse envFieldDecl ecfds

envFieldDecl :: DesugarM m => EnvFieldDecl 'Grouped -> m Core.EnvFieldDecl
envFieldDecl (EnvFieldDeclSort loc sv) = pure (Core.EnvFieldDeclSort loc sv)
envFieldDecl (EnvFieldDeclSet loc zv) = pure (Core.EnvFieldDeclSet loc zv)
