{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

module KnotSpec.Substitution where

import KnotSpec.Syntax

import           Control.Monad
import           Control.Monad.Error.Class
import           Data.Map (Map)
import qualified Data.Map as M

--------------------------------------------------------------------------------

data Substitution p =
  Substitution
  { subSortVariables    :: Map SortVariable (SymbolicTerm p)
  , subEnvVariables     :: Map EnvVariable (SymbolicEnv p)
  , subBindingVariables :: Map BindingVariable BindingVariable
  , subFreeVariables    :: Map FreeVariable (Either FreeVariable BindingVariable)
  , subSetVariables     :: Map SetVariable (SymbolicSet p)
  }

deriving instance
  ( ShowQ p
  , Show (PhFreeVariable p)
  , Show (PhBindingVariable p)
  , Show (PhSortVariable p)
  , Show (PhBindSpecInf p)
  , Show (PhRawTypeName p)
  ) => Show (Substitution p)

instance Monoid (Substitution p) where
  mempty  = Substitution mempty mempty mempty mempty mempty
  mappend (Substitution s1 e1 b1 f1 z1) (Substitution s2 e2 b2 f2 z2) =
    Substitution (s1 <> s2) (e1 <> e2) (b1 <> b2) (f1 <> f2) (z1 <> z2)

makeFunSubstitution' :: (VarResolved p, Applicative m, MonadError String m) =>
  FunField p -> SymbolicField w q -> m (Substitution q)
makeFunSubstitution' ffd fd = case ffd of
  FunFieldSort sv
    | SymFieldSort _loc _scp st <- fd ->
      pure $ mempty { subSortVariables = M.singleton sv st }
    | otherwise ->
      throwError "KnotSpec.Syntax.makeFunSubstitution'.FunFieldSort"
  FunFieldEnv ev
    | SymFieldEnv _loc _scp se <- fd ->
      pure $ mempty { subEnvVariables = M.singleton ev se }
    | otherwise ->
      throwError "KnotSpec.Syntax.makeFunSubstitution'.FunFieldEnv"
  FunFieldBinding bv
    | SymFieldBinding _loc _scp bv' <- fd ->
      pure $ mempty { subBindingVariables = M.singleton bv bv' }
    | otherwise ->
      throwError "KnotSpec.Syntax.makeFunSubstitution'.FunFieldBinding"
  FunFieldReference fv
    | SymFieldReferenceFree _loc _scp fv' <- fd ->
      pure $ mempty { subFreeVariables = M.singleton fv (Left fv') }
    | SymFieldReferenceBound _loc _scp bv' <- fd ->
      pure $ mempty { subFreeVariables = M.singleton fv (Right bv') }
    | otherwise ->
      throwError "KnotSpec.Syntax.makeFunSubstitution'.FunFieldReference"
  FunFieldSet zv
    | SymFieldSet _loc _scp sz <- fd ->
      pure $ mempty { subSetVariables = M.singleton zv sz }
    | otherwise ->
      throwError "KnotSpec.Syntax.makeFunSubstitution'.FunFieldSet"

makeFunSubstitution :: (VarResolved p, Applicative m, MonadError String m) =>
  [FunField p] -> [SymbolicField w q] -> m (Substitution q)
makeFunSubstitution ffs sfs = mconcat <$> zipWithM makeFunSubstitution' ffs sfs

makeFieldSubstitution' :: (VarResolved p, Applicative m, MonadError String m) =>
  FieldDecl w p p -> SymbolicField w q -> m (Substitution q)
makeFieldSubstitution' ffd fd = case ffd of
  FieldDeclSort _loc _bs sv
    | SymFieldSort _loc _scp st <- fd ->
      pure $ mempty { subSortVariables = M.singleton sv st }
    | otherwise ->
      throwError "KnotSpec.Syntax.makeFieldSubstitution'.FieldDeclSort"
  FieldDeclEnv _loc _bs ev
    | SymFieldEnv _loc _scp se <- fd ->
      pure $ mempty { subEnvVariables = M.singleton ev se }
    | otherwise ->
      throwError "KnotSpec.Syntax.makeFieldSubstitution'.FieldDeclEnv"
  FieldDeclBinding _loc _bs1 bv
    | SymFieldBinding _loc _scp bv' <- fd ->
      pure $ mempty { subBindingVariables = M.singleton bv bv' }
    | otherwise ->
      throwError "KnotSpec.Syntax.makeFieldSubstitution'.FieldDeclBinding"
  FieldDeclReference _loc fv
    | SymFieldReferenceFree _loc _scp fv' <- fd ->
      pure $ mempty { subFreeVariables = M.singleton fv (Left fv') }
    | SymFieldReferenceBound _loc _scp bv' <- fd ->
      pure $ mempty { subFreeVariables = M.singleton fv (Right bv') }
    | otherwise ->
      throwError "KnotSpec.Syntax.makeFieldSubstitution'.FieldDeclReference"
  FieldDeclSet _loc zv
    | SymFieldSet _loc _scp sz <- fd ->
      pure $ mempty { subSetVariables = M.singleton zv sz }
    | otherwise ->
      throwError "KnotSpec.Syntax.makeFieldSubstitution'.FieldDeclSet"

makeFieldSubstitution :: (VarResolved p, Applicative m, MonadError String m) =>
  [FieldDecl w p p] -> [SymbolicField w q] -> m (Substitution q)
makeFieldSubstitution ffs sfs = mconcat <$> zipWithM makeFieldSubstitution' ffs sfs
