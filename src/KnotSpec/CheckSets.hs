{-# LANGUAGE DataKinds #-}

module KnotSpec.CheckSets where

import           KnotSpec.Syntax

import           Control.Applicative
import           Data.Traversable

checkSetDecl :: Applicative m =>
  SetDecl 'ResolvedVars -> m (SetDecl 'Checked)
checkSetDecl (SetDecl ztn nrs ecds) =
  SetDecl ztn nrs <$> traverse checkSetCtorDecl ecds

checkSetCtorDecl :: Applicative m =>
  SetCtorDecl 'ResolvedVars -> m (SetCtorDecl 'Checked)
checkSetCtorDecl zc = case zc of
  SetCtor cn zfds ->
    SetCtor cn <$> traverse checkSetFieldDecl zfds

checkSetFieldDecl :: Applicative m =>
  SetFieldDecl 'ResolvedVars -> m (SetFieldDecl 'Checked)
checkSetFieldDecl zfd = case zfd of
  SetFieldDecl loc zv -> pure (SetFieldDecl loc zv)
