
module KnotCore.Elaboration.Fresh where

import Control.Applicative
import Control.Monad

import Data.Map (Map)
import qualified Data.Map as M

import Data.Set (Set)
import qualified Data.Set as S

import KnotCore.Syntax
import KnotCore.Elaboration.Monad
import KnotCore.Elaboration.Names

class Names a where
  collect :: a -> Set (NameRoot,Suffix)
  rename  :: Map (NameRoot,Suffix) (NameRoot,Suffix) -> a -> a

instance Names a => Names [a] where
  collect  = S.unions . map collect
  rename m = map (rename m)

instance Names MetavarVar where
  collect (MetavarVar nr suff _) = S.singleton (nr,suff)
  rename m (MetavarVar nr suff ntn) =
    case M.findWithDefault (error "rename@MetavarVar") (nr,suff) m of
      (nr',suff') -> MetavarVar nr' suff' ntn

instance Names IndexVar where
  collect (IndexVar nr suff _ _) = S.singleton (nr,suff)
  rename m (IndexVar nr suff ntn stn) =
    case M.findWithDefault (error "rename@IndexVar") (nr,suff) m of
      (nr',suff') -> IndexVar nr' suff' ntn stn

instance Names SubtreeVar where
  collect (SubtreeVar nr suff _) = S.singleton (nr,suff)
  rename m (SubtreeVar nr suff stn) =
    case M.findWithDefault (error "rename@SubtreeVar") (nr,suff) m of
      (nr',suff') -> SubtreeVar nr' suff' stn

instance Names EnvVar where
  collect (EnvVar nr suff _) = S.singleton (nr,suff)
  rename m (EnvVar nr suff etn) =
    case M.findWithDefault (error "rename@EnvVar") (nr,suff) m of
      (nr',suff') -> EnvVar nr' suff' etn

instance Names VleItem where
  collect (VleBinding _ mv) = collect mv
  collect (VleCall _ _ sv)  = collect sv
  rename m (VleBinding ntn mv) = VleBinding ntn $ rename m mv
  rename m (VleCall ntn fn sv) = VleCall ntn fn $ rename m sv

instance Names FieldDecl where
  collect (FieldSubtree sv bs) = S.unions [collect sv, collect bs]
  collect (FieldBinding mv)    = collect mv
  rename m (FieldSubtree sv bs) = FieldSubtree (rename m sv) (rename m bs)
  rename m (FieldBinding mv)    = FieldBinding (rename m mv)

instance Names CtorDecl where
  collect (CtorVar _ mv)      = collect mv
  collect (CtorTerm _ fds)    = collect fds
  rename m (CtorVar cn mv)    = CtorVar cn $ rename m mv
  rename m (CtorTerm cn  fds) = CtorTerm cn $ rename m fds

freshen' :: (Names a, Elab m) => a -> m a
freshen' a = do
  let ns = S.toList $ collect a
  m <- forM ns $ \n@(nr,suff) -> do
         suff' <- freshSuffix nr suff
         return (n,(nr,suff'))
  return (rename (M.fromList m) a)

class Freshen a where
  freshen :: Elab m => a -> m a
instance Freshen a => Freshen [a] where
  freshen = mapM freshen
instance Freshen MetavarVar where
  freshen (MetavarVar nr suff ntn) =
    do
      suff' <- freshSuffix nr suff
      return $ MetavarVar nr suff' ntn
instance Freshen IndexVar where
  freshen (IndexVar nr suff ntn stn) =
    do
      suff' <- freshSuffix nr suff
      return $ IndexVar nr suff' ntn stn
instance Freshen SubtreeVar where
  freshen (SubtreeVar nr suff stn) =
    do
      suff' <- freshSuffix nr suff
      return $ SubtreeVar nr suff' stn
instance Freshen EnvVar where
  freshen (EnvVar nr suff etn) =
    do
      suff' <- freshSuffix nr suff
      return $ EnvVar nr suff' etn
instance Freshen FieldMetaBinding where
  freshen (FieldMetaBindingSubtree name) = FieldMetaBindingSubtree <$> freshen name
  freshen (FieldMetaBindingMetavar name) = FieldMetaBindingMetavar <$> freshen name
  freshen (FieldMetaBindingOutput name) = FieldMetaBindingOutput <$> freshen name

instance Freshen CtorDecl where
  freshen = freshen'

{-
  freshen (CtorVar cn mv) = CtorVar cn <$> freshen mv
  freshen (CtorTerm cn fds) =
    do
      ren1 <- [ do
                  sv' <- freshen sv
                  return (sv,sv')
              | FieldSubtree sv _ <- fds
              ]
      ren2 <- [ do
                  mv' <- freshen mv
                  return (mv,mv')
              | FieldBinding mv <- fds
              ]

      CtorTerm cn <$> mapM freshen fds
-}

freshSubtreeVar :: Elab m => SortTypeName -> m SubtreeVar
freshSubtreeVar stn =
  do
    nrs <- getSortRoots stn
    freshen $
      SubtreeVar
        (head nrs)
        ""
        stn

freshIndexVar :: Elab m => NamespaceTypeName -> m IndexVar
freshIndexVar ntn =
  do
    nrs <- getNamespaceRoots ntn
    (stn,_) <- getNamespaceCtor ntn
    freshen $
      IndexVar (head nrs) "" ntn stn

freshEnvVar :: Elab m => EnvTypeName -> m EnvVar
freshEnvVar etn =
  do
    nrs <- getEnvRoots etn
    freshen (EnvVar (head nrs) "" etn)

freshCutoffVar :: Elab m => NamespaceTypeName -> m CutoffVar
freshCutoffVar ntn =
  do
    let nr = NR "c"
    suff <- freshSuffix nr ""
    return (CV nr suff ntn)

freshTraceVar :: Elab m => NamespaceTypeName -> m TraceVar
freshTraceVar ntn =
  do
    let nr = NR "d"
    suff <- freshSuffix nr ""
    return (TV nr suff ntn)

freshHVarlistVar :: Elab m => m HVarlistVar
freshHVarlistVar =
  do
    let nr = NR "k"
    suff <- freshSuffix nr ""
    return (HVLV nr suff)

-- freshVarlist :: Elab m => NamespaceTypeName -> m Varlist
-- freshVarlist ntn =
--   do
--     let nr = NR "k"
--     suff <- freshSuffix nr ""
--     return (Varlist nr suff ntn)

freshInductionHypothesis :: Elab m => SubtreeVar -> m Hypothesis
freshInductionHypothesis (SubtreeVar (NR nr) suff _) =
  do
    let ihnr = NR $ "IH" ++ nr
    suff <- freshSuffix ihnr suff
    return (Hypothesis ihnr suff)
