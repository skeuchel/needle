{-# LANGUAGE DataKinds #-}

module KnotCore.Environment where

import           Knot.Env
import           KnotCore.Syntax

import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Maybe (catMaybes)
import qualified Data.Set as S

--  __  __     _                      _                            _
-- |  \/  |___| |_ __ _   ___ _ ___ _(_)_ _ ___ _ _  _ __  ___ _ _| |_ ___
-- | |\/| / -_)  _/ _` | / -_) ' \ V / | '_/ _ \ ' \| '  \/ -_) ' \  _(_-<
-- |_|  |_\___|\__\__,_| \___|_||_\_/|_|_| \___/_||_|_|_|_\___|_||_\__/__/

type MENamespaceRoots         = Map NamespaceTypeName [NameRoot]
type MENamespaceShiftRoot     = Map NamespaceTypeName String
type MENamespaceSubstRoot     = Map NamespaceTypeName String
type MENamespaceCtor          = Map NamespaceTypeName (SortTypeName,CtorName)
-- FIXME: There could be multiple environments defined
type MENamespaceEnvCtor       = Map NamespaceTypeName (EnvTypeName,CtorName)
type MESortRoots              = Map SortTypeName [NameRoot]
type MESortNamespaceDeps      = Map SortTypeName [NamespaceTypeName]
type MESortGroupOfSort        = Map SortTypeName SortGroupTypeName
type MECtorSort               = Map CtorName SortTypeName
type MECtorRegFields          = Map CtorName [FieldDecl 'WMV]
type MEFunType                = Map FunName (SortTypeName,[NamespaceTypeName])
type MEEnvRoots               = Map EnvTypeName [NameRoot]
type MEEnvNil                 = Map EnvTypeName CtorName
type MEEnvCtors               = Map EnvTypeName [EnvCtor]
type MEEnvNamespaceDeps       = Map EnvTypeName [NamespaceTypeName]
type MERelationRulesNames     = Map RelationTypeName [CtorName]
type MERelationEnvTypeNames   = Map RelationTypeName EnvTypeName
type MESortVariablePos        = Map SortVariable SortVariablePos

data MetaEnvironments =
  MetaEnvironments
  { meNamespaceRoots        :: MENamespaceRoots
  , meNamespaceShiftRoot    :: MENamespaceShiftRoot
  , meNamespaceSubstRoot    :: MENamespaceSubstRoot
  , meNamespaceCtor         :: MENamespaceCtor
  , meNamespaceEnvCtor      :: MENamespaceEnvCtor
  , meSortRoots             :: MESortRoots
  , meSortNamespaceDeps     :: MESortNamespaceDeps
  , meSortGroupOfSort       :: MESortGroupOfSort
  , meCtorSort              :: MECtorSort
  , meCtorRegFields         :: MECtorRegFields
  , meFunType               :: MEFunType
  , meEnvRoots              :: MEEnvRoots
  , meEnvNil                :: MEEnvNil
  , meEnvCtors              :: MEEnvCtors
  , meEnvNamespaceDeps      :: MEEnvNamespaceDeps
  , meRelationRuleNames     :: MERelationRulesNames
  , meRelationEnvTypeNames  :: MERelationEnvTypeNames
  }
  deriving (Show)

{-
makeGlobalEnv :: TermSpec -> GlobalEnv
makeGlobalEnv (TermSpec nds _ sgds fgds eds rgds zgds) =
  let sds  = concatMap sgSorts sgds
      fds  = concatMap snd $ concatMap fgdFuns fgds
      rds  = concatMap rgRelations rgds
      zds  = concatMap zgdSets zgds
      ndRoots = [ (nsdTypeName nd, nsdNameRoots nd) | nd <- nds ]
      sdRoots = [ (sdTypeName sd, sdNameRoots sd) | sd <- sds ]
      edRoots = [ (edTypeName ed, edNameRoots ed) | ed <- eds ]
      rdRoots = [ (relTypeName rd, relNameRoots rd) | rd <- rds ]
      zdRoots = [ (zdTypeName zd, zdNameRoots zd) | zd <- zds ]
  in
    GlobalEnv
      (M.fromList
         [ (nsdTypeName nd, Just (nsdSort nd))
         | nd <- nds
         ])
      (M.fromList
         [ (fdName fd, (fdSource fd, fdTarget fd))
         | fd <- fds
         ])
      -- (M.fromList
      --    [ ((edTypeName ed,typeNameOf bv), map typeNameOf svs)
      --    | ed <- eds, EnvCtorCons _cn bv svs <- edCtors ed
      --    ])
      (M.fromList
         [ (relTypeName rd, (typeNameOf <$> relEnv rd, typeNameOf <$> relIndices rd))
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
      --    [ ((fn,relTypeName rd), etn)
      --    | rd <- rds, (fn,etn) <- relOutputs rd
      --    ])
      (M.fromList
         [ (relTypeName rd, relOutputs rd)
         | rd <- rds
         ])
      (M.fromList
         [ (sdTypeName sd, map ctorDeclName $ sdCtors sd)
         | sd <- sds
         ])
      (M.fromList $ concat
         [ [ (nr, ResNTN ntn) | (ntn,nrs) <- ndRoots, nr <- nrs ]
         , [ (nr, ResSTN stn) | (stn,nrs) <- sdRoots, nr <- nrs ]
         , [ (nr, ResETN etn) | (etn,nrs) <- edRoots, nr <- nrs ]
         , [ (nr, ResRTN rtn) | (rtn,nrs) <- rdRoots, nr <- nrs ]
         ])
-}

metaEnvironments :: TermSpec -> MetaEnvironments
metaEnvironments ts =
  MetaEnvironments
  { meNamespaceRoots       = M.fromList
                                 [ (nsdTypeName nd,nsdNameRoots nd)
                                 | nd <- nds
                                 ]
  , meNamespaceShiftRoot   = M.fromList
                                 [ (nsdTypeName nd,nsdShiftRoot nd)
                                 | nd <- nds
                                 ]
  , meNamespaceSubstRoot   = M.fromList
                                 [ (nsdTypeName nd,nsdSubstRoot nd)
                                 | nd <- nds
                                 ]
  , meNamespaceCtor        = M.fromList
                                 [ (typeNameOf (ctorDeclFreeVariable cd), (typeNameOf sd, ctorDeclName cd))
                                 | sg <- sgs, sd <- sgSorts sg, cd@CtorVar{} <- sdCtors sd
                                 ]
  , meSortRoots            = M.fromList
                                 [ (sdTypeName sd,sdNameRoots sd)
                                 | sg <- sgs, sd <- sgSorts sg
                                 ]
  , meSortGroupOfSort      = M.fromList
                                 [ (sdTypeName sd,sgTypeName sg)
                                 | sg <- sgs, sd <- sgSorts sg
                                 ]
  , meSortNamespaceDeps    = meSortNamespaceDeps'
  , meCtorSort             = M.fromList
                                 [ (ctorDeclName cd, sdTypeName sd)
                                 | sg <- sgs, sd <- sgSorts sg, cd <- sdCtors sd
                                 ]
  , meCtorRegFields        = M.fromList
                                 [ (ctorDeclName cd, ctorDeclFields cd)
                                 | sg <- sgs, sd <- sgSorts sg, cd@CtorReg{} <- sdCtors sd
                                 ]
  , meFunType              = M.fromList
                                 [ (fdName fd, (stn, fdTarget fd))
                                 | fgd <- fgds, (stn,fds) <- fgdFuns fgd, fd <- fds
                                 ]
  , meEnvRoots             = M.fromList
                                 [ (edTypeName ed,edNameRoots ed)
                                 | ed <- eds
                                 ]
  , meEnvCtors             = M.fromList
                                 [ (edTypeName ed,edCtors ed)
                                 | ed <- eds
                                 ]
  , meNamespaceEnvCtor     = M.fromList
                                 [ (typeNameOf (envCtorBindingVariable ec), (typeNameOf ed, envCtorName ec))
                                 | ed <- eds, ec@EnvCtorCons{} <- edCtors ed
                                 ]
  , meEnvNil               = M.fromList
                                 [ (typeNameOf ed, envCtorName ec)
                                 | ed <- eds, ec@EnvCtorNil{} <- edCtors ed
                                 ]
  -- TODO: Update
  , meEnvNamespaceDeps     = M.fromList
                                 [ let stns =
                                         uniq
                                           [ typeNameOf sv
                                           | EnvCtorCons _ _ svs _mbRtno <- edCtors ed
                                           , FieldDeclSort _ sv _ <- svs
                                           ]
                                       ntns =
                                         uniq . concat $ catMaybes
                                           [ M.lookup stn meSortNamespaceDeps'
                                           | stn <- stns
                                           ]
                                   in (typeNameOf ed, ntns)
                                 | ed <- eds
                                 ]
  , meRelationRuleNames    = M.fromList
                                 [ (relTypeName rd, map ruleName $ relRules rd)
                                 | rd <- concatMap rgRelations rgds
                                 ]
  , meRelationEnvTypeNames = M.fromList
                                 [ (rtn, typeNameOf ev)
                                 | RelationGroupDecl _ rds <- rgds
                                 , RelationDecl (Just ev) rtn _ _ _ _ <- rds
                                 ]
    }
  where nds  = tsNamespaceDecls ts
        sgs  = tsSortGroupDecls ts
        fgds = tsFunGroupDecls ts
        eds  = tsEnvDecls ts
        rgds = tsRelGroupDecls ts
        uniq :: Ord a => [a] -> [a]
        uniq = S.toList . S.fromList
        meSortNamespaceDeps' =
          M.fromList
            [ (sdTypeName sd,sgNamespaces sg)
            | sg <- sgs, sd <- sgSorts sg
            ]

mkMESortVariablePos :: [Formula] -> MESortVariablePos
mkMESortVariablePos fmls =
  M.fromList
    [ (sv,SortVariablePos jmtVar rbs jmt pre sct post)
    | FormJudgement jmtVar rbs jmt _outs <- fmls
    , let sfs = jmtFields jmt
    , (pre,sf:post) <- map (`splitAt` sfs) [0..length sfs-1]
    , (sv,sct) <- M.toList (field sf)
    ]
  where
    term :: SymbolicTerm -> Map SortVariable SymbolicCoTerm
    term (SymSubtree _ sv) = M.singleton sv (SymCoHole (typeNameOf sv))
    term (SymCtorReg scp cn sfs) =
      M.unions
        [ fmap (\sct -> SymCoCtorReg scp bs cn pre sct post) (term st)
        | (pre,SymFieldSort _ bs st:post) <-
          map (`splitAt`sfs) [0..length sfs - 1]
        ]
    term _                 = M.empty

    field :: SymbolicField w -> Map SortVariable SymbolicCoTerm
    field (SymFieldSort _scp _bs st) = term st
    field _ = M.empty
