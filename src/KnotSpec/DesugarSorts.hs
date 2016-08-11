{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}

module KnotSpec.DesugarSorts where

import           Knot.Env
import           Knot.Fresh
import           KnotSpec.Syntax hiding (envCtorName)
import           KnotSpec.Environment

import qualified KnotCore.Syntax as Core
import qualified KnotCore.Elaboration.Fresh as Core

import           Control.Monad.Error.Class
import qualified Data.Foldable as F
import           Data.List (intercalate)
import qualified Data.Map as M
import           Data.Maybe
import           Data.Monoid ((<>))

--------------------------------------------------------------------------------

type DesugarM m = (MonadError String m, EnvM m, FreshM m)

--------------------------------------------------------------------------------

namespaceDecl :: DesugarM m => MECtorVars 'Grouped ->
  NamespaceDecl 'Grouped -> m Core.NamespaceDecl
namespaceDecl me (NamespaceDecl _ ntn nrs (Just stn) dirs _) = do
  cn <- maybe
          (throwError $
             "No variable constructor for namespace " <> toIdent ntn)
          return
          (M.lookup ntn me)
  shiftName <-
    case [s | NamespaceShift s <- dirs] of
      []  -> return $ "shift_" <> toIdent ntn <> "_"
      [s] -> return s
      ss  -> throwError $ "more than one shift root defined: " <>
               intercalate ", " ss
  substName <-
    case [s | NamespaceSubst s <- dirs] of
      []  -> return $ "subst_" <> toIdent ntn <> "_"
      [s] -> return s
      ss  -> throwError $ "more than one subst root defined: " <>
               intercalate ", " ss
  return $! Core.NamespaceDecl ntn nrs stn cn
             shiftName substName
namespaceDecl _me (NamespaceDecl _ _ _ Nothing _ _) =
  error "KnotSpec.Desugar.nameSpaceDecl.Nothing"

--------------------------------------------------------------------------------

sortGroupDecl :: DesugarM m => SortGroupDecl 'Grouped -> m Core.SortGroupDecl
sortGroupDecl (SortGroupDecl sgtn sds ntns hasBs) =
  Core.SortGroupDecl (Core.SGTN $ toIdent sgtn)
    <$> traverse sortDecl sds
    <*> pure ntns
    <*> pure hasBs

sortDecl :: DesugarM m => SortDecl 'Grouped -> m Core.SortDecl
sortDecl (SortDecl stn nrs cds) =
  Core.SortDecl stn nrs <$> traverse ctorDecl cds

ctorDecl :: DesugarM m => CtorDecl 'Grouped -> m Core.CtorDecl
ctorDecl cd = case cd of
  CtorVar cn fv -> Core.CtorVar cn fv <$> Core.freshHypothesis
  CtorReg cn fds -> Core.CtorReg cn <$> traverse fieldDecl fds

fieldDecl :: DesugarM m => FieldDecl w 'Grouped 'Grouped -> m (Core.FieldDecl w)
fieldDecl (FieldDeclSort _loc bs sv)   =
  Core.FieldDeclSort
    <$> bindSpec bs
    <*> pure sv
    <*> Core.freshHypothesis
fieldDecl (FieldDeclEnv{}) = error "NOT_IMPLEMENTED"
fieldDecl (FieldDeclBinding _loc bs bv) =
  Core.FieldDeclBinding
    <$> bindSpec bs
    <*> pure bv
fieldDecl (FieldDeclReference _ _) = error "NOT_IMPLEMENTED"

bindSpec :: DesugarM m => BindSpec 'Grouped -> m Core.BindSpec
bindSpec = traverse bindSpecItem

bindSpecItem :: DesugarM m => BindSpecItem 'Grouped -> m Core.BindSpecItem
bindSpecItem (BsiCall fn sv) = pure (Core.BsiCall fn sv)
bindSpecItem (BsiBinding bv) = pure (Core.BsiBinding bv)

--------------------------------------------------------------------------------

funGroupDecl :: DesugarM m => FunGroupDecl 'Grouped -> m Core.FunGroupDecl
funGroupDecl (FunGroupDecl fgtn sgtn funs) =
  Core.FunGroupDecl
    <$> pure fgtn
    <*> pure sgtn
    <*> sequenceA
        [ (,) <$> pure stn <*> traverse funDecl fds
        | (stn,fds) <- funs
        ]

funDecl :: DesugarM m => FunDecl 'Grouped -> m Core.FunDecl
funDecl (FunDecl fn stn ntns cases) =
  Core.FunDecl fn stn ntns <$> traverse funCase cases

funCase :: DesugarM m => FunCase 'Grouped -> m Core.FunCase
funCase (FunCase cn ffds rhs) =
  Core.FunCase cn
    <$> traverse funField ffds
    <*> bindSpec rhs

funField :: DesugarM m => FunField 'Grouped -> m Core.FunField
funField ff = case ff of
  FunFieldSort sv      -> Core.FunFieldSort Nil <$> pure sv
  FunFieldReference fv -> Core.FunFieldReference <$> pure fv
  FunFieldBinding bv   -> Core.FunFieldBinding Nil <$> pure bv
  FunFieldEnv ev       -> Core.FunFieldEnv Nil <$> pure ev

--------------------------------------------------------------------------------

envDecl :: DesugarM m => [RelationDecl 'Grouped] -> EnvDecl 'Grouped -> m Core.EnvDecl
envDecl rds (EnvDecl etn nrs ecds) =
  Core.EnvDecl etn nrs <$> traverse (envCtorDecl rds) ecds

envCtorDecl :: DesugarM m => [RelationDecl 'Grouped] -> EnvCtorDecl 'Grouped -> m Core.EnvCtor
envCtorDecl rds ecd = case ecd of
  EnvCtorNil cn -> pure (Core.EnvCtorNil cn)
  EnvCtorCons cn bv ecfds mbRtn ->
    Core.EnvCtorCons cn bv
      <$> traverse fieldDecl ecfds
      <*> pure
          (flip fmap mbRtn $ \rtn ->
             Core.EnvCtorSubst rtn $
               listToMaybe
                 [ cn
                 | rd <- rds
                 , rdTypeName rd == rtn
                 , RuleVar cn _ _ _ _ _ <- rdRules rd
                 ]
          )

--------------------------------------------------------------------------------

setGroupDecl :: DesugarM m => SetGroupDecl 'Grouped -> m Core.SetGroupDecl
setGroupDecl (SetGroupDecl zds) = Core.SetGroupDecl <$> traverse setDecl zds

setDecl :: DesugarM m => SetDecl 'Grouped -> m Core.SetDecl
setDecl (SetDecl etn nrs ecds) =
  Core.SetDecl etn nrs <$> traverse setCtorDecl ecds

setCtorDecl :: DesugarM m => SetCtorDecl 'Grouped -> m Core.SetCtorDecl
setCtorDecl (SetCtor cn zfds) =
  Core.SetCtor cn <$> traverse setFieldDecl zfds

setFieldDecl :: DesugarM m => SetFieldDecl 'Grouped -> m Core.SetFieldDecl
setFieldDecl (SetFieldDecl loc zv) = pure (Core.SetFieldDecl loc zv)
