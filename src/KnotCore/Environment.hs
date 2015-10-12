
module KnotCore.Environment where

import Data.Map (Map)
import qualified Data.Map as M

import Data.Set (Set)
import qualified Data.Set as S

import Data.Maybe

import KnotCore.Syntax


--  __  __     _                      _                            _
-- |  \/  |___| |_ __ _   ___ _ ___ _(_)_ _ ___ _ _  _ __  ___ _ _| |_ ___
-- | |\/| / -_)  _/ _` | / -_) ' \ V / | '_/ _ \ ' \| '  \/ -_) ' \  _(_-<
-- |_|  |_\___|\__\__,_| \___|_||_\_/|_|_| \___/_||_|_|_|_\___|_||_\__/__/

type MENamespaceRoots         = Map NamespaceTypeName [NameRoot]
type MENamespaceShiftRoot     = Map NamespaceTypeName String
type MENamespaceSubstRoot     = Map NamespaceTypeName String
type MENamespaceCtor          = Map NamespaceTypeName (SortTypeName,CtorName)
-- FIXME: There could be multiple environments  defined
type MENamespaceEnvCtor       = Map NamespaceTypeName (EnvTypeName,CtorName)
type MESortRoots              = Map SortTypeName [NameRoot]
type MESortNamespaceDeps      = Map SortTypeName [NamespaceTypeName]
type MESortGroupOfSort        = Map SortTypeName SortGroupTypeName
type MECtorSort               = Map CtorName SortTypeName
type MEFunType                = Map FunName (SortTypeName,[NamespaceTypeName])
type MEEnvRoots               = Map EnvTypeName [NameRoot]
type MEEnvCtors               = Map EnvTypeName [EnvCtor]
type MEEnvNamespaceDeps       = Map EnvTypeName [NamespaceTypeName]

data MetaEnvironments =
  MetaEnvironments {
    meNamespaceRoots        :: MENamespaceRoots,
    meNamespaceShiftRoot    :: MENamespaceShiftRoot,
    meNamespaceSubstRoot    :: MENamespaceSubstRoot,
    meNamespaceCtor         :: MENamespaceCtor,
    meNamespaceEnvCtor      :: MENamespaceEnvCtor,
    meSortRoots             :: MESortRoots,
    meSortNamespaceDeps     :: MESortNamespaceDeps,
    meSortGroupOfSort       :: MESortGroupOfSort,
    meCtorSort              :: MECtorSort,
    meFunType               :: MEFunType,
    meEnvRoots              :: MEEnvRoots,
    meEnvCtors              :: MEEnvCtors,
    meEnvNamespaceDeps      :: MEEnvNamespaceDeps
  }
  deriving (Show)

metaEnvironments :: TermSpec -> MetaEnvironments
metaEnvironments ts =
    MetaEnvironments {
      meNamespaceRoots     = M.fromList
                               [ (nsdTypeName nd,nsdNameRoots nd)
                               | nd <- nds
                               ],
      meNamespaceShiftRoot = M.fromList
                               [ (nsdTypeName nd,nsdShiftRoot nd)
                               | nd <- nds
                               ],
      meNamespaceSubstRoot = M.fromList
                               [ (nsdTypeName nd,nsdSubstRoot nd)
                               | nd <- nds
                               ],
      meNamespaceCtor      = M.fromList
                               [ (typeNameOf (cdMetavar cd), (typeNameOf sd, cdName cd))
                               | sg <- sgs, sd <- sgSorts sg, cd@CtorVar{} <- sdCtors sd
                               ],
      meSortRoots          = M.fromList
                               [ (sdTypeName sd,sdNameRoots sd)
                               | sg <- sgs, sd <- sgSorts sg
                               ],
      meSortGroupOfSort    = M.fromList
                               [ (sdTypeName sd,sgTypeName sg)
                               | sg <- sgs, sd <- sgSorts sg
                               ],
      meSortNamespaceDeps  = meSortNamespaceDeps,
      meCtorSort           = M.fromList
                               [ (cdName cd, sdTypeName sd)
                               | sg <- sgs, sd <- sgSorts sg, cd <- sdCtors sd
                               ],
      meFunType            = M.fromList
                               [ (fdName fd, (stn, fdTarget fd))
                               | fgd <- fgds, (stn,fds) <- fgdFuns fgd, fd <- fds
                               ],
      meEnvRoots           = M.fromList
                               [ (edTypeName ed,edNameRoots ed)
                               | ed <- eds
                               ],
      meEnvCtors           = M.fromList
                               [ (edTypeName ed,edCtors ed)
                               | ed <- eds
                               ],
      meNamespaceEnvCtor   = M.fromList
                               [ (typeNameOf (ecMetavar ec), (typeNameOf ed, ecName ec))
                               | ed <- eds, ec@EnvCtorCons{} <- edCtors ed
                               ],
      meEnvNamespaceDeps   = M.fromList
                               [ let stns =
                                       uniq
                                         [ typeNameOf sv
                                         | EnvCtorCons _ _ svs <- edCtors ed, sv <- svs
                                         ]
                                     ntns =
                                       uniq . concat $ catMaybes
                                         [ M.lookup stn meSortNamespaceDeps
                                         | stn <- stns
                                         ]
                                 in (typeNameOf ed, ntns)
                               | ed <- eds
                               ]
    }
  where nds  = tsNamespaceDecls ts
        sgs  = tsSortGroupDecls ts
        fgds = tsFunGroupDecls ts
        eds  = tsEnvDecls ts
        uniq :: Ord a => [a] -> [a]
        uniq = S.toList . S.fromList
        meSortNamespaceDeps =
          M.fromList
            [ (sdTypeName sd,sgNamespaces sg)
            | sg <- sgs, sd <- sgSorts sg
            ]
