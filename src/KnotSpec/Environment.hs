{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

module KnotSpec.Environment where

import           Knot.Env
import           KnotSpec.Syntax

import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Maybe

--  __  __     _                      _                            _
-- |  \/  |___| |_ __ _   ___ _ ___ _(_)_ _ ___ _ _  _ __  ___ _ _| |_ ___
-- | |\/| / -_)  _/ _` | / -_) ' \ V / | '_/ _ \ ' \| '  \/ -_) ' \  _(_-<
-- |_|  |_\___|\__\__,_| \___|_||_\_/|_|_| \___/_||_|_|_|_\___|_||_\__/__/

-- | Maps namespacenameroots to the canonical namespacenameroot.
type MENamespaceTypeName p  = Map NameRoot (PhNamespaceTypeName p)
-- | Maps fieldnameroots to the typename.
type MESortTypeName p       = Map NameRoot (PhSortTypeName p)
-- | Maps constructor names to their types
type MECtorType p           = Map CtorName (PhSortTypeName p)
-- | Maps namespacenames to (sortname,ctorvarname)
type MEFunType p            = Map
                                FunName
                                (PhSortTypeName p,[PhNamespaceTypeName p])
-- | Maps envnameroots to the canonical envnameroot.
type MEEnvTypeName p        = Map NameRoot (PhEnvTypeName p)

type MECtorVars p           = Map (PhNamespaceTypeName p) CtorName
type MESortGroupOfSort p    = Map (PhSortTypeName p) SortGroupTypeName
type MECtorRegFields p      = Map CtorName [FieldDecl 'WMV p p]

type MECtorDecl p           = Map
                                CtorName
                                (CtorDecl p)
type MERelationType p       = Map
                                (PhRelationTypeName p)
                                (Maybe (PhEnvTypeName p), [PhFieldTypeName 'WOMV p])
type MERelationDecl p       = Map (PhRelationTypeName p) (RelationDecl p)

-- -- | Maps relationtypenames to envtypenames
-- type MERelationEnv            = Map TypeName TypeName

data MetaEnvironments p =
  MetaEnvironments
  { meNamespaceTypeName  :: MENamespaceTypeName p
  , meSortTypeName       :: MESortTypeName p
  , meSortGroupOfSort    :: MESortGroupOfSort p
  , meFunType            :: MEFunType p
  , meEnvTypeName        :: MEEnvTypeName p
  , meCtorVars           :: MECtorVars p
  , meCtorRegFields      :: MECtorRegFields p
  , meCtorType           :: MECtorType p
  }

deriving instance
  ( ShowQ p
  ) => Show (MetaEnvironments p)

type Ords p =
  ( Ord (PhNamespaceTypeName p)
  , Ord (PhSortTypeName p)
  , Ord (PhEnvTypeName p)
  )

mkMetaEnvironments :: (IsGrouped p, Ords p) =>
  SPhase p -> TermSpec p -> MetaEnvironments p
mkMetaEnvironments phase (ts :: TermSpec p) =
  let nds   = tsNamespaceDecls ts
      sgds  = tsSortGroupDecls ts
      fgds  = tsFunGroupDecls ts
      eds   = tsEnvDecls ts
      sds   = concatMap sgdSorts sgds
  in MetaEnvironments
     { meNamespaceTypeName = mkMENamespaceTypeName nds
     , meSortTypeName      = mkMESortTypeName sds
     , meFunType           = mkMEFunType fgds
     , meEnvTypeName       = mkMEEnvTypeName eds
     , meSortGroupOfSort   = mkMESortGroupOfSort phase sgds
     , meCtorVars          = mkMECtorVars phase sds
     , meCtorRegFields     = mkMECtorRegFields sds
     , meCtorType          = mkMECtorType sds
     }

mkMENamespaceTypeName :: [NamespaceDecl p] -> MENamespaceTypeName p
mkMENamespaceTypeName nds =
  M.fromList
  [ (nr,ndTypeName nd)
  | nd <- nds
  , nr <- ndNameRoots nd
  ]

mkMESortTypeName :: [SortDecl p] -> MESortTypeName p
mkMESortTypeName sds =
  M.fromList
  [ (nr,sdTypeName sd)
  | sd <- sds
  , nr <- sdNameRoots sd
  ]

mkMEFunType :: [FunGroupDecl p] -> MEFunType p
mkMEFunType fgds =
  M.fromList
    [ fnType fd
    | FunGroupDecl _ _ stnFdss <- fgds,
      (_stn,fds) <- stnFdss,
      fd <- fds
    ]
  where
    fnType :: FunDecl p -> (FunName, (PhSortTypeName p,[PhNamespaceTypeName p]))
    fnType fd = (fdName fd, (fdSource fd, fdTarget fd))

mkMEEnvTypeName :: [EnvDecl p] -> MEEnvTypeName p
mkMEEnvTypeName eds =
  M.fromList
  [ (nr,edTypeName ed)
  | ed <- eds
  , nr <- edNameRoots ed
  ]

mkMECtorVars :: Ord (PhNamespaceTypeName p) => SPhase p -> [SortDecl p] -> MECtorVars p
mkMECtorVars phase sds =
  M.fromList $ catMaybes
  [ case phase of
      SParsed         -> Nothing
      SResolvedTypes  -> Nothing
      SResolvedVars   -> Just (fvNtn fv, cn)
      SChecked        -> Just (fvNtn fv, cn)
      SGrouped        -> Just (fvNtn fv, cn)
  | sd <- sds
  , CtorVar cn fv <- sdCtors sd
  ]

mkMESortGroupOfSort :: SPhase p -> [SortGroupDecl p] -> MESortGroupOfSort p
mkMESortGroupOfSort phase sgds =
  case phase of
    SGrouped   -> M.fromList
      [ (stn, sgtn)
      | SortGroupDecl sgtn sds _ _ <- sgds
      , SortDecl stn _ _ <- sds
      ]
    _          -> error "[INTERNAL] Accessing SortGroups before grouping"

mkMECtorRegFields :: [SortDecl p] -> MECtorRegFields p
mkMECtorRegFields sds =
  M.fromList [ (cn, fds) | sd <- sds, CtorReg cn fds <- sdCtors sd ]

mkMECtorType :: [SortDecl p] -> MECtorType p
mkMECtorType sds =
  M.fromList [ (ctorDeclName cd, sdTypeName sd) | sd <- sds, cd <- sdCtors sd ]

meCtorDecl :: [SortDecl p] -> MECtorDecl p
meCtorDecl sds =
  M.fromList [ (ctorDeclName cd, cd) | sd <- sds, cd <- sdCtors sd ]

-- meRelationType :: Ord (PhRelationTypeName p) => [RelationDecl p] -> MERelationType p
-- meRelationType rds =
--   M.fromList [ (rdTypeName rd, (rdEnv rd, rdIndices rd)) | rd <- rds ]

meRelationDecl :: Ord (PhRelationTypeName p) => [RelationDecl p] -> MERelationDecl p
meRelationDecl rds =
  M.fromList [ (rdTypeName rd, rd) | rd <- rds ]

makeGlobalEnv' :: forall p. TypeResolved p => [NamespaceDecl p] -> [SortDecl p] ->
  [EnvDecl p] -> [FunDecl p] -> [SetDecl p] -> [RelationDecl p] -> GlobalEnv
makeGlobalEnv' nds sds eds fds zds rds =
  let ndRoots = [ (ndTypeName nd, ndNameRoots nd) | nd <- nds ]
      sdRoots = [ (sdTypeName sd, sdNameRoots sd) | sd <- sds ]
      edRoots = [ (edTypeName ed, edNameRoots ed) | ed <- eds ]
      rdRoots = [ (rdTypeName rd, rdNameRoots rd) | rd <- rds ]
      zdRoots = [ (zdTypeName zd, zdNameRoots zd) | zd <- zds ]
  in
    GlobalEnv
      (M.fromList
         [ (ndTypeName nd, ndSort nd)
         | nd <- nds
         ])
      (M.fromList
         [ (fdName fd, (fdSource fd, fdTarget fd))
         | fd <- fds
         ])
      (M.fromList
         [ ((edTypeName ed,ntn), (map typeNameOf fds, mbRtn))
         | ed <- eds, EnvCtorCons _cn bv fds mbRtn <- edCtors ed
         , let ntn = case checkP (sphase :: SPhase p) of
                       LeftC
                         | RawVar _ _ (ResNTN ntn) <- bv -> ntn
                         | otherwise -> error ""
                       RightC -> typeNameOf bv
         ])
      (M.fromList
         [ (rdTypeName rd, (rdEnv rd, map typeNameOf (rdIndices rd)))
         | rd <- rds
         ])
      (M.fromList ndRoots)
      (M.fromList sdRoots)
      (M.fromList edRoots)
      (M.fromList rdRoots)
      (M.fromList zdRoots)
      (M.fromList
         [ (ctorDeclName cd, sdTypeName sd)
         | sd <- sds, cd <- sdCtors sd
         ])
      -- (M.fromList
      --    [ ((fn,rdTypeName rd), etn)
      --    | rd <- rds, (fn,etn) <- rdOutputs rd
      --    ])
      (M.fromList
         [ (rdTypeName rd, rdOutputs rd)
         | rd <- rds
         ])
      (M.fromList
         [ (sdTypeName sd, map ctorDeclName $ sdCtors sd)
         | sd <- sds
         ])
      -- (M.fromList $ concat
      --    [ [ (nr, ResNTN ntn) | (ntn,nrs) <- ndRoots, nr <- nrs ]
      --    , [ (nr, ResSTN stn) | (stn,nrs) <- sdRoots, nr <- nrs ]
      --    , [ (nr, ResETN etn) | (etn,nrs) <- edRoots, nr <- nrs ]
      --    , [ (nr, ResRTN rtn) | (rtn,nrs) <- rdRoots, nr <- nrs ]
      --    , [ (nr, ResZTN ztn) | (ztn,nrs) <- zdRoots, nr <- nrs ]
      --    ])

makeGlobalEnv :: TypeResolved p => TermSpec p -> GlobalEnv
makeGlobalEnv ts = case ts of
  TermSpec nds sds eds fds rds zds ->
    makeGlobalEnv' nds sds eds fds zds rds
  TermSpecGrouped nds sgds eds fgds rgds zgds ->
    makeGlobalEnv' nds
      (concatMap sgdSorts sgds) eds
      (concatMap snd $ concatMap fgdFunDecls fgds)
      (concatMap zgdSets zgds)
      (concatMap rgdRelations rgds)
  TermSpecRaw decls ->
    makeGlobalEnv' nds sds eds fds zds rds
    where
      nds = [ nd | ND nd <- decls ]
      sds = [ sd | SD sd <- decls ]
      eds = [ ed | ED ed <- decls ]
      fds = [ fd | FD fd <- decls ]
      zds = [ zd | ZD zd <- decls ]
      rds = [ rd | RD rd <- decls ]

makeSubstitutableClauses ::
  VarResolved q =>
  [EnvDecl q] ->
  [RelationDecl q] ->
  [SubstitutableClauseInfo]
makeSubstitutableClauses eds rds =
  [ SubstitutableClauseInfo
      (envCtorName ec) rtn
      (listToMaybe [ ruleName vr | vr@RuleVar{} <- rdRules rd ])
      [ ruleName r
      | r@RuleReg{} <- rdRules rd
      , not . null $ [ () | RuleMetavarFree{} <- ruleMetavarBinders r]
      ]
  | ed <- eds, ec@EnvCtorCons{envCtorHypo = Just rtn} <- edCtors ed
  , rd <- rds, rdTypeName rd == rtn
  ]
