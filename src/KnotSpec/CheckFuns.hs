{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module KnotSpec.CheckFuns where

import           KnotSpec.Syntax

-- Function declarations are checked for sort correctness during name
-- resolution and they are checked for scope correctness when checking
-- constructor declerations of sorts.

checkFunDecl :: Applicative m => FunDecl 'ResolvedVars -> m (FunDecl 'Checked)
checkFunDecl (FunDecl fn stn ntns cases) =
  FunDecl fn stn ntns <$> traverse checkFunCase cases

checkFunCase :: Applicative m => FunCase 'ResolvedVars -> m (FunCase 'Checked)
checkFunCase (FunCase cn ffd rhs) =
  FunCase cn
    <$> traverse checkFunField ffd
    <*> checkBindSpec rhs

checkFunField :: Applicative m =>
  FunField 'ResolvedVars -> m (FunField 'Checked)
checkFunField ff = case ff of
  FunFieldSort sv -> pure (FunFieldSort sv)
  FunFieldReference fv -> pure (FunFieldReference fv)
  FunFieldBinding bv -> pure (FunFieldBinding bv)
  FunFieldEnv ev -> pure (FunFieldEnv ev)
  FunFieldSet zv -> pure (FunFieldSet zv)

checkBindSpec :: Applicative m =>
  BindSpec 'ResolvedVars -> m (BindSpec 'Checked)
checkBindSpec = traverse checkBindSpecItem

checkBindSpecItem :: Applicative m =>
  BindSpecItem 'ResolvedVars -> m (BindSpecItem 'Checked)
checkBindSpecItem (BsiBinding bv) = pure (BsiBinding bv)
checkBindSpecItem (BsiCall fn sv) = pure (BsiCall fn sv)
