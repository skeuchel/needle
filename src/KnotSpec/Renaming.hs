{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module KnotSpec.Renaming where

import KnotSpec.Syntax

import           Control.Monad
import           Control.Monad.Error.Class
import           Data.Map (Map)
import qualified Data.Map as M

--------------------------------------------------------------------------------

data Renaming =
  Renaming
  { renSortVariables    :: Map SortVariable SortVariable
  , renEnvVariables     :: Map EnvVariable EnvVariable
  , renBindingVariables :: Map BindingVariable BindingVariable
  , renFreeVariables    :: Map FreeVariable FreeVariable
  }
  deriving Show

instance Monoid Renaming where
  mempty  = Renaming M.empty M.empty M.empty M.empty
  mappend (Renaming s1 e1 b1 f1) (Renaming s2 e2 b2 f2) =
    Renaming (s1 <> s2) (e1 <> e2) (b1 <> b2) (f1 <> f2)

makeRenaming' :: (VarResolved p, Applicative m, MonadError String m) => FunField p -> FieldDecl 'WMV p p -> m Renaming
makeRenaming' ffd fd = case (ffd,fd) of
  (FunFieldSort sv,    FieldDeclSort _loc _bs' sv')    ->
    pure $ mempty { renSortVariables = M.singleton sv sv' }
  (FunFieldEnv ev,     FieldDeclEnv _loc _bs' ev')     ->
    pure $ mempty { renEnvVariables = M.singleton ev ev' }
  (FunFieldBinding bv, FieldDeclBinding _loc _bs' bv') ->
    pure $ mempty { renBindingVariables = M.singleton bv bv' }
  (FunFieldReference fv,  FieldDeclReference _loc fv')   ->
    pure $ mempty { renFreeVariables = M.singleton fv fv' }
  _ -> throwError "makeRenaming: IMPOSSIBLE"

makeRenaming :: (VarResolved p, Applicative m, MonadError String m) => [FunField p] -> [FieldDecl 'WMV p p] -> m Renaming
makeRenaming ffs fds = mconcat <$> zipWithM makeRenaming' ffs fds

renameBindSpec :: (VarResolved p, Applicative m, MonadError String m) =>
  Renaming -> BindSpec p -> m (BindSpec p)
renameBindSpec ren = traverse (renameBindSpecItem ren)

renameBindSpecItem :: (VarResolved p, Applicative m, MonadError String m) =>
  Renaming -> BindSpecItem p -> m (BindSpecItem p)
renameBindSpecItem ren bsi
  | BsiBinding bv <- bsi,
    Just bv' <- M.lookup bv (renBindingVariables ren)
  = pure (BsiBinding bv')
  | BsiCall fn sv <- bsi,
    Just sv' <- M.lookup sv (renSortVariables ren)
  = pure (BsiCall fn sv')
  | otherwise
  = throwError "KnotSpec.Syntax.renameBindSpecItem: IMPOSSIBLE"
