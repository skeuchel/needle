

{-# OPTIONS_GHC -fno-warn-dodgy-imports -fno-warn-unused-matches #-}
-- UUAGC 0.9.52.1 (src/KnotSpec/AG.ag)
module KnotSpec.AG where

import KnotSpec.Syntax

import qualified Data.Map

{-# LINE 3 "src/KnotSpec/Desugaring.ag" #-}

import qualified KnotCore.Syntax as Core
import qualified KnotCore.Analysis as Core

import Control.Applicative
import Control.Monad.Error.Class
import Data.Graph (flattenSCC, stronglyConnComp)
import Data.List (intercalate)
import Data.Maybe (catMaybes)
import Data.Map (Map)
import Data.Set (Set)
import qualified Data.Map
import qualified Data.Set
{-# LINE 26 "src/KnotSpec/AG.hs" #-}

{-# LINE 9 "src/KnotSpec/Syntax.ag" #-}

import KnotSpec.Syntax.Core
import Data.Map (Map)
{-# LINE 32 "src/KnotSpec/AG.hs" #-}
{-# LINE 18 "src/KnotSpec/Desugaring.ag" #-}

{- This is the type-checking monad for the surface language.
   At the moment it only keeps track of errors. Environments
   are handled by the attribute grammar.
-}

type TcM = Either String
consA :: (Applicative f) => f a -> f [a] -> f [a]
consA = liftA2 (:)

mappendA :: (Applicative f, Monoid m) => f m -> f m -> f m
mappendA = liftA2 mappend

memptyA :: (Applicative f, Monoid m) => f m
memptyA = pure mempty

{-
lookupNamespaceTypeName
  :: NameRoot
  -> MENamespaceTypeName
  -> TcM TypeName
lookupNamespaceTypeName nnr me =
  maybe
    (throwError $
     "Did not find canonical namespacename for root" ++ fromNR nnr)
    return
    (lookup nnr me)

lookupSortTypeName
  :: NameRoot
  -> MESortTypeName
  -> TcM TypeName
lookupSortTypeName fnr me =
  maybe
    (throwError $
     "Did not find typename for root" ++ fromNR fnr)
    return
    (lookup fnr me)
-}

lookupFunType
  :: FunName
  -> MEFunType
  -> TcM (Core.SortTypeName,[Core.NamespaceTypeName])
lookupFunType fn me =
  maybe
    (throwError $
     "Did not find function type for " ++ fn)
    (\(stn,ntns) -> return (Core.STN (fromTN stn), map (Core.NTN . fromTN) ntns))
    (Data.Map.lookup fn me)
  where fromTN (TN tn) = tn
data CoreTypeName
  = NTN Core.NamespaceTypeName
  | STN Core.SortTypeName
  | ETN Core.EnvTypeName

data CoreFieldName
  = FRN Core.MetavarVar
  | FRS Core.SubtreeVar
{-# LINE 93 "src/KnotSpec/AG.hs" #-}

{-# LINE 204 "src/KnotSpec/Desugaring.ag" #-}

desugarTermSpec :: TermSpec -> TcM Core.TermSpec
desugarTermSpec ts = Core.analyze <$> desugared_Syn_TermSpec sem
  where sem = wrap_TermSpec (sem_TermSpec ts) defaultValues
{-# LINE 100 "src/KnotSpec/AG.hs" #-}

{-# LINE 462 "src/KnotSpec/Desugaring.ag" #-}

-- This defines a node 'Core.SortName' in the graph with
-- label 'DN' and adjacent nodes 'Core.SortNames'.
type DepNode =
  (DN,
   Core.SortTypeName,
   [Core.SortTypeName]
  )
-- The label includes the desugared SortDecl, the sort and
-- namespace dependencies.
type DN  =
  (Core.SortDecl,
   Set Core.SortTypeName,
   Set Core.NamespaceTypeName
  )
{-# LINE 118 "src/KnotSpec/AG.hs" #-}

{-# LINE 530 "src/KnotSpec/Desugaring.ag" #-}

-- A strongly connected component with combined labels.
type DNG =
  ([Core.SortDecl],
   Set Core.SortTypeName,
   Set Core.NamespaceTypeName
  )

sortDepAnalysis :: [DepNode] -> [DNG]
sortDepAnalysis = map (flattenDNS . flattenSCC) . stronglyConnComp

flattenDNS :: [DN] -> DNG
flattenDNS dns = (sds, Data.Set.unions sortDeps, Data.Set.unions namespaceDeps)
  where (sds,sortDeps,namespaceDeps) = unzip3 dns

-- This function folds the strongly connected components in topological
-- order. It builds a mapping [SortName -> Set NamespaceName] so that the
-- namespace dependencies for each component can be resolved.
namespaceDepAnalysis' :: [DNG] -> Map Core.SortTypeName (Set Core.NamespaceTypeName) -> [Core.SortGroupDecl]
namespaceDepAnalysis' []                                              namespaceDepAcc = []
namespaceDepAnalysis' ((sortDecls,sortNames,namespaceDepDirect):dngs) namespaceDepAcc = res
  where
    -- These are the namespace dependencies we inherit from the sort
    -- dependencies.
    namespaceDepIndirect :: Set Core.NamespaceTypeName
    namespaceDepIndirect = Data.Set.unions $ catMaybes
                             [ Data.Map.lookup sortName namespaceDepAcc
                             | sortName <- Data.Set.toList sortNames
                             ]

    -- The final set is the union of direct and indirect dependencies
    namespaceDepFinal :: Set Core.NamespaceTypeName
    namespaceDepFinal = Data.Set.union namespaceDepDirect namespaceDepIndirect

    -- This is the namespace dependency mapping for each sort declaration in
    -- this group.
    namespaceDepAcc' :: Map Core.SortTypeName (Set Core.NamespaceTypeName)
    namespaceDepAcc' = Data.Map.fromList
                         [ (sortName,namespaceDepFinal)
                         | (Core.SortDecl sortName _ _) <- sortDecls
                         ]

    -- The group of sort declarations that we construct for the current
    -- component.
    sgtn :: Core.SortGroupTypeName
    sgtn = Core.groupName (map Core.typeNameOf sortDecls)
    hasBindspecs :: Bool
    hasBindspecs = not . null $
                     [ ()
                     | sd <- sortDecls
                     , Core.CtorTerm _ fds <- Core.sdCtors sd
                     , Core.FieldSubtree _ (_:_) <- fds
                     ]
    sg :: Core.SortGroupDecl
    sg = Core.SortGroupDecl
           sgtn
           sortDecls
           (Data.Set.toList namespaceDepFinal)
           hasBindspecs

    res = sg : namespaceDepAnalysis' dngs (Data.Map.union namespaceDepAcc' namespaceDepAcc)

namespaceDepAnalysis :: [DNG] -> [Core.SortGroupDecl]
namespaceDepAnalysis dngs = namespaceDepAnalysis' dngs mempty

dependencyAnalysis :: [DepNode] -> [Core.SortGroupDecl]
dependencyAnalysis = namespaceDepAnalysis . sortDepAnalysis
{-# LINE 188 "src/KnotSpec/AG.hs" #-}

{-# LINE 2 "src/KnotSpec/Environment.ag" #-}

data MetaEnvironments =
  MetaEnvironments {
    meNamespaceNameRoots :: MENamespaceNameRoots,
    meNamespaceTypeName  :: MENamespaceTypeName,
    meSortNameRoots      :: MESortNameRoots,
    meSortTypeName       :: MESortTypeName,
    meNamespaceCtor      :: MENamespaceCtor,
    meEnvNameRoots       :: MEEnvNameRoots,
    meEnvTypeName        :: MEEnvTypeName,
    meFunType            :: MEFunType,
    meRelationEnv        :: MERelationEnv
  }
  deriving (Show)

metaEnvironments :: TermSpec -> MetaEnvironments
metaEnvironments ts = metaEnvironments_Syn_TermSpec sem
  where sem = wrap_TermSpec (sem_TermSpec ts) defaultValues

defaultValues :: Inh_TermSpec
defaultValues = (Inh_TermSpec {})
{-# LINE 212 "src/KnotSpec/AG.hs" #-}

{-# LINE 16 "src/KnotSpec/AG.ag" #-}

fromTN :: TypeName -> String
fromTN (TN s) = s
{-# LINE 218 "src/KnotSpec/AG.hs" #-}
-- BindSpec ----------------------------------------------------
-- cata
sem_BindSpec :: BindSpec ->
                T_BindSpec
sem_BindSpec list =
    (Prelude.foldr sem_BindSpec_Cons sem_BindSpec_Nil (Prelude.map sem_VleItem list))
-- semantic domain
type T_BindSpec = MEEnvNameRoots ->
                  MEEnvTypeName ->
                  MEFunType ->
                  MENamespaceCtor ->
                  MENamespaceNameRoots ->
                  MENamespaceTypeName ->
                  MERelationEnv ->
                  MESortNameRoots ->
                  MESortTypeName ->
                  ( (TcM Core.BindSpec),BindSpec)
data Inh_BindSpec = Inh_BindSpec {meEnvNameRoots_Inh_BindSpec :: MEEnvNameRoots,meEnvTypeName_Inh_BindSpec :: MEEnvTypeName,meFunType_Inh_BindSpec :: MEFunType,meNamespaceCtor_Inh_BindSpec :: MENamespaceCtor,meNamespaceNameRoots_Inh_BindSpec :: MENamespaceNameRoots,meNamespaceTypeName_Inh_BindSpec :: MENamespaceTypeName,meRelationEnv_Inh_BindSpec :: MERelationEnv,meSortNameRoots_Inh_BindSpec :: MESortNameRoots,meSortTypeName_Inh_BindSpec :: MESortTypeName}
data Syn_BindSpec = Syn_BindSpec {desugared_Syn_BindSpec :: (TcM Core.BindSpec),self_Syn_BindSpec :: BindSpec}
wrap_BindSpec :: T_BindSpec ->
                 Inh_BindSpec ->
                 Syn_BindSpec
wrap_BindSpec sem (Inh_BindSpec _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName) =
    (let ( _lhsOdesugared,_lhsOself) = sem _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName
     in  (Syn_BindSpec _lhsOdesugared _lhsOself))
sem_BindSpec_Cons :: T_VleItem ->
                     T_BindSpec ->
                     T_BindSpec
sem_BindSpec_Cons hd_ tl_ =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOdesugared :: (TcM Core.BindSpec)
              _lhsOself :: BindSpec
              _hdOmeEnvNameRoots :: MEEnvNameRoots
              _hdOmeEnvTypeName :: MEEnvTypeName
              _hdOmeFunType :: MEFunType
              _hdOmeNamespaceCtor :: MENamespaceCtor
              _hdOmeNamespaceNameRoots :: MENamespaceNameRoots
              _hdOmeNamespaceTypeName :: MENamespaceTypeName
              _hdOmeRelationEnv :: MERelationEnv
              _hdOmeSortNameRoots :: MESortNameRoots
              _hdOmeSortTypeName :: MESortTypeName
              _tlOmeEnvNameRoots :: MEEnvNameRoots
              _tlOmeEnvTypeName :: MEEnvTypeName
              _tlOmeFunType :: MEFunType
              _tlOmeNamespaceCtor :: MENamespaceCtor
              _tlOmeNamespaceNameRoots :: MENamespaceNameRoots
              _tlOmeNamespaceTypeName :: MENamespaceTypeName
              _tlOmeRelationEnv :: MERelationEnv
              _tlOmeSortNameRoots :: MESortNameRoots
              _tlOmeSortTypeName :: MESortTypeName
              _hdIdesugared :: (TcM Core.VleItem)
              _hdIself :: VleItem
              _tlIdesugared :: (TcM Core.BindSpec)
              _tlIself :: BindSpec
              _lhsOdesugared =
                  ({-# LINE 180 "src/KnotSpec/Desugaring.ag" #-}
                   (consA _hdIdesugared _tlIdesugared)
                   {-# LINE 284 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _hdOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 293 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 298 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 303 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 308 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 313 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 318 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 323 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 328 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 333 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 338 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 343 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 348 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 353 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 358 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 363 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 368 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 373 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 378 "src/KnotSpec/AG.hs" #-}
                   )
              ( _hdIdesugared,_hdIself) =
                  hd_ _hdOmeEnvNameRoots _hdOmeEnvTypeName _hdOmeFunType _hdOmeNamespaceCtor _hdOmeNamespaceNameRoots _hdOmeNamespaceTypeName _hdOmeRelationEnv _hdOmeSortNameRoots _hdOmeSortTypeName
              ( _tlIdesugared,_tlIself) =
                  tl_ _tlOmeEnvNameRoots _tlOmeEnvTypeName _tlOmeFunType _tlOmeNamespaceCtor _tlOmeNamespaceNameRoots _tlOmeNamespaceTypeName _tlOmeRelationEnv _tlOmeSortNameRoots _tlOmeSortTypeName
          in  ( _lhsOdesugared,_lhsOself)))
sem_BindSpec_Nil :: T_BindSpec
sem_BindSpec_Nil =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOdesugared :: (TcM Core.BindSpec)
              _lhsOself :: BindSpec
              _lhsOdesugared =
                  ({-# LINE 180 "src/KnotSpec/Desugaring.ag" #-}
                   memptyA
                   {-# LINE 401 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  []
              _lhsOself =
                  _self
          in  ( _lhsOdesugared,_lhsOself)))
-- CtorDecl ----------------------------------------------------
-- cata
sem_CtorDecl :: CtorDecl ->
                T_CtorDecl
sem_CtorDecl (CtorVar _ctorName _ctorMetavar) =
    (sem_CtorDecl_CtorVar _ctorName (sem_Name _ctorMetavar))
sem_CtorDecl (CtorTerm _ctorName _ctorFields) =
    (sem_CtorDecl_CtorTerm _ctorName (sem_FieldDecls _ctorFields))
-- semantic domain
type T_CtorDecl = (Core.SortTypeName) ->
                  MEEnvNameRoots ->
                  MEEnvTypeName ->
                  MEFunType ->
                  MENamespaceCtor ->
                  MENamespaceNameRoots ->
                  MENamespaceTypeName ->
                  MERelationEnv ->
                  MESortNameRoots ->
                  MESortTypeName ->
                  TypeName ->
                  ( (TcM Core.CtorDecl),(TcM [Core.NamespaceTypeName]),(TcM Core.FunctionEnv),CtorDecl,MENamespaceCtor,(TcM [Core.SortTypeName]))
data Inh_CtorDecl = Inh_CtorDecl {coreSortTypeName_Inh_CtorDecl :: (Core.SortTypeName),meEnvNameRoots_Inh_CtorDecl :: MEEnvNameRoots,meEnvTypeName_Inh_CtorDecl :: MEEnvTypeName,meFunType_Inh_CtorDecl :: MEFunType,meNamespaceCtor_Inh_CtorDecl :: MENamespaceCtor,meNamespaceNameRoots_Inh_CtorDecl :: MENamespaceNameRoots,meNamespaceTypeName_Inh_CtorDecl :: MENamespaceTypeName,meRelationEnv_Inh_CtorDecl :: MERelationEnv,meSortNameRoots_Inh_CtorDecl :: MESortNameRoots,meSortTypeName_Inh_CtorDecl :: MESortTypeName,sortTypeName_Inh_CtorDecl :: TypeName}
data Syn_CtorDecl = Syn_CtorDecl {desugared_Syn_CtorDecl :: (TcM Core.CtorDecl),namespaceDependencies_Syn_CtorDecl :: (TcM [Core.NamespaceTypeName]),sFunctionDef_Syn_CtorDecl :: (TcM Core.FunctionEnv),self_Syn_CtorDecl :: CtorDecl,smeNamespaceCtor_Syn_CtorDecl :: MENamespaceCtor,sortDependencies_Syn_CtorDecl :: (TcM [Core.SortTypeName])}
wrap_CtorDecl :: T_CtorDecl ->
                 Inh_CtorDecl ->
                 Syn_CtorDecl
wrap_CtorDecl sem (Inh_CtorDecl _lhsIcoreSortTypeName _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName _lhsIsortTypeName) =
    (let ( _lhsOdesugared,_lhsOnamespaceDependencies,_lhsOsFunctionDef,_lhsOself,_lhsOsmeNamespaceCtor,_lhsOsortDependencies) = sem _lhsIcoreSortTypeName _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName _lhsIsortTypeName
     in  (Syn_CtorDecl _lhsOdesugared _lhsOnamespaceDependencies _lhsOsFunctionDef _lhsOself _lhsOsmeNamespaceCtor _lhsOsortDependencies))
sem_CtorDecl_CtorVar :: CtorName ->
                        T_Name ->
                        T_CtorDecl
sem_CtorDecl_CtorVar ctorName_ ctorMetavar_ =
    (\ _lhsIcoreSortTypeName
       _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName
       _lhsIsortTypeName ->
         (let _lhsOnamespaceDependencies :: (TcM [Core.NamespaceTypeName])
              _lhsOsmeNamespaceCtor :: MENamespaceCtor
              _lhsOsFunctionDef :: (TcM Core.FunctionEnv)
              _lhsOsortDependencies :: (TcM [Core.SortTypeName])
              _lhsOself :: CtorDecl
              _lhsOdesugared :: (TcM Core.CtorDecl)
              _ctorMetavarOmeEnvNameRoots :: MEEnvNameRoots
              _ctorMetavarOmeEnvTypeName :: MEEnvTypeName
              _ctorMetavarOmeFunType :: MEFunType
              _ctorMetavarOmeNamespaceCtor :: MENamespaceCtor
              _ctorMetavarOmeNamespaceNameRoots :: MENamespaceNameRoots
              _ctorMetavarOmeNamespaceTypeName :: MENamespaceTypeName
              _ctorMetavarOmeRelationEnv :: MERelationEnv
              _ctorMetavarOmeSortNameRoots :: MESortNameRoots
              _ctorMetavarOmeSortTypeName :: MESortTypeName
              _ctorMetavarIcoreFieldName :: (TcM CoreFieldName)
              _ctorMetavarIcoreTypeName :: (TcM CoreTypeName)
              _ctorMetavarIfieldMetaBinding :: (TcM Core.FieldMetaBinding)
              _ctorMetavarImetavarName :: (TcM Core.MetavarVar)
              _ctorMetavarInamespaceTypeName :: (TcM Core.NamespaceTypeName)
              _ctorMetavarIroot :: NameRoot
              _ctorMetavarIself :: Name
              _ctorMetavarIsubtreeName :: (TcM Core.SubtreeVar)
              _ctorMetavarIsuffix :: String
              _desugared =
                  ({-# LINE 255 "src/KnotSpec/Desugaring.ag" #-}
                   Core.CtorVar (Core.CNS ctorName_ _lhsIcoreSortTypeName)
                     <$> _ctorMetavarImetavarName
                   {-# LINE 480 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOnamespaceDependencies =
                  ({-# LINE 489 "src/KnotSpec/Desugaring.ag" #-}
                   do
                     coreTypeName <- _ctorMetavarIcoreTypeName
                     case coreTypeName of
                       NTN ntn -> return [ntn]
                       _       -> return []
                   {-# LINE 489 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOsmeNamespaceCtor =
                  ({-# LINE 152 "src/KnotSpec/Environment.ag" #-}
                   case Data.Map.lookup _ctorMetavarIroot _lhsImeNamespaceTypeName of
                     Just typeName ->
                       Data.Map.singleton
                         typeName
                         (_lhsIsortTypeName,ctorName_)
                     Nothing ->
                       error $
                         "Did not find canonical namespacename for root" ++
                         fromNR _ctorMetavarIroot
                   {-# LINE 502 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOsFunctionDef =
                  ({-# LINE 603 "src/KnotSpec/Desugaring.ag" #-}
                   memptyA
                   {-# LINE 507 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOsortDependencies =
                  ({-# LINE 480 "src/KnotSpec/Desugaring.ag" #-}
                   memptyA
                   {-# LINE 512 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  CtorVar ctorName_ _ctorMetavarIself
              _lhsOself =
                  _self
              _lhsOdesugared =
                  ({-# LINE 173 "src/KnotSpec/Desugaring.ag" #-}
                   _desugared
                   {-# LINE 521 "src/KnotSpec/AG.hs" #-}
                   )
              _ctorMetavarOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 526 "src/KnotSpec/AG.hs" #-}
                   )
              _ctorMetavarOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 531 "src/KnotSpec/AG.hs" #-}
                   )
              _ctorMetavarOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 536 "src/KnotSpec/AG.hs" #-}
                   )
              _ctorMetavarOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 541 "src/KnotSpec/AG.hs" #-}
                   )
              _ctorMetavarOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 546 "src/KnotSpec/AG.hs" #-}
                   )
              _ctorMetavarOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 551 "src/KnotSpec/AG.hs" #-}
                   )
              _ctorMetavarOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 556 "src/KnotSpec/AG.hs" #-}
                   )
              _ctorMetavarOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 561 "src/KnotSpec/AG.hs" #-}
                   )
              _ctorMetavarOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 566 "src/KnotSpec/AG.hs" #-}
                   )
              ( _ctorMetavarIcoreFieldName,_ctorMetavarIcoreTypeName,_ctorMetavarIfieldMetaBinding,_ctorMetavarImetavarName,_ctorMetavarInamespaceTypeName,_ctorMetavarIroot,_ctorMetavarIself,_ctorMetavarIsubtreeName,_ctorMetavarIsuffix) =
                  ctorMetavar_ _ctorMetavarOmeEnvNameRoots _ctorMetavarOmeEnvTypeName _ctorMetavarOmeFunType _ctorMetavarOmeNamespaceCtor _ctorMetavarOmeNamespaceNameRoots _ctorMetavarOmeNamespaceTypeName _ctorMetavarOmeRelationEnv _ctorMetavarOmeSortNameRoots _ctorMetavarOmeSortTypeName
          in  ( _lhsOdesugared,_lhsOnamespaceDependencies,_lhsOsFunctionDef,_lhsOself,_lhsOsmeNamespaceCtor,_lhsOsortDependencies)))
sem_CtorDecl_CtorTerm :: CtorName ->
                         T_FieldDecls ->
                         T_CtorDecl
sem_CtorDecl_CtorTerm ctorName_ ctorFields_ =
    (\ _lhsIcoreSortTypeName
       _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName
       _lhsIsortTypeName ->
         (let _lhsOnamespaceDependencies :: (TcM [Core.NamespaceTypeName])
              _lhsOsFunctionDef :: (TcM Core.FunctionEnv)
              _lhsOsmeNamespaceCtor :: MENamespaceCtor
              _lhsOsortDependencies :: (TcM [Core.SortTypeName])
              _lhsOself :: CtorDecl
              _lhsOdesugared :: (TcM Core.CtorDecl)
              _ctorFieldsOmeEnvNameRoots :: MEEnvNameRoots
              _ctorFieldsOmeEnvTypeName :: MEEnvTypeName
              _ctorFieldsOmeFunType :: MEFunType
              _ctorFieldsOmeNamespaceCtor :: MENamespaceCtor
              _ctorFieldsOmeNamespaceNameRoots :: MENamespaceNameRoots
              _ctorFieldsOmeNamespaceTypeName :: MENamespaceTypeName
              _ctorFieldsOmeRelationEnv :: MERelationEnv
              _ctorFieldsOmeSortNameRoots :: MESortNameRoots
              _ctorFieldsOmeSortTypeName :: MESortTypeName
              _ctorFieldsIdesugared :: (TcM [Core.FieldDecl])
              _ctorFieldsInamespaceDependencies :: (TcM [Core.NamespaceTypeName])
              _ctorFieldsIself :: FieldDecls
              _ctorFieldsIsortDependencies :: (TcM [Core.SortTypeName])
              _desugared =
                  ({-# LINE 258 "src/KnotSpec/Desugaring.ag" #-}
                   Core.CtorTerm (Core.CNS ctorName_ _lhsIcoreSortTypeName)
                     <$> _ctorFieldsIdesugared
                   {-# LINE 609 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOnamespaceDependencies =
                  ({-# LINE 483 "src/KnotSpec/Desugaring.ag" #-}
                   _ctorFieldsInamespaceDependencies
                   {-# LINE 614 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOsFunctionDef =
                  ({-# LINE 603 "src/KnotSpec/Desugaring.ag" #-}
                   memptyA
                   {-# LINE 619 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOsmeNamespaceCtor =
                  ({-# LINE 143 "src/KnotSpec/Environment.ag" #-}
                   mempty
                   {-# LINE 624 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOsortDependencies =
                  ({-# LINE 480 "src/KnotSpec/Desugaring.ag" #-}
                   _ctorFieldsIsortDependencies
                   {-# LINE 629 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  CtorTerm ctorName_ _ctorFieldsIself
              _lhsOself =
                  _self
              _lhsOdesugared =
                  ({-# LINE 173 "src/KnotSpec/Desugaring.ag" #-}
                   _desugared
                   {-# LINE 638 "src/KnotSpec/AG.hs" #-}
                   )
              _ctorFieldsOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 643 "src/KnotSpec/AG.hs" #-}
                   )
              _ctorFieldsOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 648 "src/KnotSpec/AG.hs" #-}
                   )
              _ctorFieldsOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 653 "src/KnotSpec/AG.hs" #-}
                   )
              _ctorFieldsOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 658 "src/KnotSpec/AG.hs" #-}
                   )
              _ctorFieldsOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 663 "src/KnotSpec/AG.hs" #-}
                   )
              _ctorFieldsOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 668 "src/KnotSpec/AG.hs" #-}
                   )
              _ctorFieldsOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 673 "src/KnotSpec/AG.hs" #-}
                   )
              _ctorFieldsOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 678 "src/KnotSpec/AG.hs" #-}
                   )
              _ctorFieldsOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 683 "src/KnotSpec/AG.hs" #-}
                   )
              ( _ctorFieldsIdesugared,_ctorFieldsInamespaceDependencies,_ctorFieldsIself,_ctorFieldsIsortDependencies) =
                  ctorFields_ _ctorFieldsOmeEnvNameRoots _ctorFieldsOmeEnvTypeName _ctorFieldsOmeFunType _ctorFieldsOmeNamespaceCtor _ctorFieldsOmeNamespaceNameRoots _ctorFieldsOmeNamespaceTypeName _ctorFieldsOmeRelationEnv _ctorFieldsOmeSortNameRoots _ctorFieldsOmeSortTypeName
          in  ( _lhsOdesugared,_lhsOnamespaceDependencies,_lhsOsFunctionDef,_lhsOself,_lhsOsmeNamespaceCtor,_lhsOsortDependencies)))
-- CtorDecls ---------------------------------------------------
-- cata
sem_CtorDecls :: CtorDecls ->
                 T_CtorDecls
sem_CtorDecls list =
    (Prelude.foldr sem_CtorDecls_Cons sem_CtorDecls_Nil (Prelude.map sem_CtorDecl list))
-- semantic domain
type T_CtorDecls = (Core.SortTypeName) ->
                   MEEnvNameRoots ->
                   MEEnvTypeName ->
                   MEFunType ->
                   MENamespaceCtor ->
                   MENamespaceNameRoots ->
                   MENamespaceTypeName ->
                   MERelationEnv ->
                   MESortNameRoots ->
                   MESortTypeName ->
                   TypeName ->
                   ( (TcM [Core.CtorDecl]),(TcM [Core.NamespaceTypeName]),(TcM Core.FunctionEnv),CtorDecls,MENamespaceCtor,(TcM [Core.SortTypeName]))
data Inh_CtorDecls = Inh_CtorDecls {coreSortTypeName_Inh_CtorDecls :: (Core.SortTypeName),meEnvNameRoots_Inh_CtorDecls :: MEEnvNameRoots,meEnvTypeName_Inh_CtorDecls :: MEEnvTypeName,meFunType_Inh_CtorDecls :: MEFunType,meNamespaceCtor_Inh_CtorDecls :: MENamespaceCtor,meNamespaceNameRoots_Inh_CtorDecls :: MENamespaceNameRoots,meNamespaceTypeName_Inh_CtorDecls :: MENamespaceTypeName,meRelationEnv_Inh_CtorDecls :: MERelationEnv,meSortNameRoots_Inh_CtorDecls :: MESortNameRoots,meSortTypeName_Inh_CtorDecls :: MESortTypeName,sortTypeName_Inh_CtorDecls :: TypeName}
data Syn_CtorDecls = Syn_CtorDecls {desugared_Syn_CtorDecls :: (TcM [Core.CtorDecl]),namespaceDependencies_Syn_CtorDecls :: (TcM [Core.NamespaceTypeName]),sFunctionDef_Syn_CtorDecls :: (TcM Core.FunctionEnv),self_Syn_CtorDecls :: CtorDecls,smeNamespaceCtor_Syn_CtorDecls :: MENamespaceCtor,sortDependencies_Syn_CtorDecls :: (TcM [Core.SortTypeName])}
wrap_CtorDecls :: T_CtorDecls ->
                  Inh_CtorDecls ->
                  Syn_CtorDecls
wrap_CtorDecls sem (Inh_CtorDecls _lhsIcoreSortTypeName _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName _lhsIsortTypeName) =
    (let ( _lhsOdesugared,_lhsOnamespaceDependencies,_lhsOsFunctionDef,_lhsOself,_lhsOsmeNamespaceCtor,_lhsOsortDependencies) = sem _lhsIcoreSortTypeName _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName _lhsIsortTypeName
     in  (Syn_CtorDecls _lhsOdesugared _lhsOnamespaceDependencies _lhsOsFunctionDef _lhsOself _lhsOsmeNamespaceCtor _lhsOsortDependencies))
sem_CtorDecls_Cons :: T_CtorDecl ->
                      T_CtorDecls ->
                      T_CtorDecls
sem_CtorDecls_Cons hd_ tl_ =
    (\ _lhsIcoreSortTypeName
       _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName
       _lhsIsortTypeName ->
         (let _lhsOdesugared :: (TcM [Core.CtorDecl])
              _lhsOnamespaceDependencies :: (TcM [Core.NamespaceTypeName])
              _lhsOsFunctionDef :: (TcM Core.FunctionEnv)
              _lhsOsmeNamespaceCtor :: MENamespaceCtor
              _lhsOsortDependencies :: (TcM [Core.SortTypeName])
              _lhsOself :: CtorDecls
              _hdOcoreSortTypeName :: (Core.SortTypeName)
              _hdOmeEnvNameRoots :: MEEnvNameRoots
              _hdOmeEnvTypeName :: MEEnvTypeName
              _hdOmeFunType :: MEFunType
              _hdOmeNamespaceCtor :: MENamespaceCtor
              _hdOmeNamespaceNameRoots :: MENamespaceNameRoots
              _hdOmeNamespaceTypeName :: MENamespaceTypeName
              _hdOmeRelationEnv :: MERelationEnv
              _hdOmeSortNameRoots :: MESortNameRoots
              _hdOmeSortTypeName :: MESortTypeName
              _hdOsortTypeName :: TypeName
              _tlOcoreSortTypeName :: (Core.SortTypeName)
              _tlOmeEnvNameRoots :: MEEnvNameRoots
              _tlOmeEnvTypeName :: MEEnvTypeName
              _tlOmeFunType :: MEFunType
              _tlOmeNamespaceCtor :: MENamespaceCtor
              _tlOmeNamespaceNameRoots :: MENamespaceNameRoots
              _tlOmeNamespaceTypeName :: MENamespaceTypeName
              _tlOmeRelationEnv :: MERelationEnv
              _tlOmeSortNameRoots :: MESortNameRoots
              _tlOmeSortTypeName :: MESortTypeName
              _tlOsortTypeName :: TypeName
              _hdIdesugared :: (TcM Core.CtorDecl)
              _hdInamespaceDependencies :: (TcM [Core.NamespaceTypeName])
              _hdIsFunctionDef :: (TcM Core.FunctionEnv)
              _hdIself :: CtorDecl
              _hdIsmeNamespaceCtor :: MENamespaceCtor
              _hdIsortDependencies :: (TcM [Core.SortTypeName])
              _tlIdesugared :: (TcM [Core.CtorDecl])
              _tlInamespaceDependencies :: (TcM [Core.NamespaceTypeName])
              _tlIsFunctionDef :: (TcM Core.FunctionEnv)
              _tlIself :: CtorDecls
              _tlIsmeNamespaceCtor :: MENamespaceCtor
              _tlIsortDependencies :: (TcM [Core.SortTypeName])
              _lhsOdesugared =
                  ({-# LINE 172 "src/KnotSpec/Desugaring.ag" #-}
                   (consA _hdIdesugared _tlIdesugared)
                   {-# LINE 773 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOnamespaceDependencies =
                  ({-# LINE 483 "src/KnotSpec/Desugaring.ag" #-}
                   (mappendA _hdInamespaceDependencies _tlInamespaceDependencies)
                   {-# LINE 778 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOsFunctionDef =
                  ({-# LINE 603 "src/KnotSpec/Desugaring.ag" #-}
                   (liftA2 (Data.Map.unionWith Data.Map.union) _hdIsFunctionDef _tlIsFunctionDef)
                   {-# LINE 783 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOsmeNamespaceCtor =
                  ({-# LINE 143 "src/KnotSpec/Environment.ag" #-}
                   (Data.Map.unionWith (error "smeVariableCtor union") _hdIsmeNamespaceCtor _tlIsmeNamespaceCtor)
                   {-# LINE 788 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOsortDependencies =
                  ({-# LINE 480 "src/KnotSpec/Desugaring.ag" #-}
                   (mappendA _hdIsortDependencies _tlIsortDependencies)
                   {-# LINE 793 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _hdOcoreSortTypeName =
                  ({-# LINE 243 "src/KnotSpec/Desugaring.ag" #-}
                   _lhsIcoreSortTypeName
                   {-# LINE 802 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 807 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 812 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 817 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 822 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 827 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 832 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 837 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 842 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 847 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOsortTypeName =
                  ({-# LINE 135 "src/KnotSpec/Environment.ag" #-}
                   _lhsIsortTypeName
                   {-# LINE 852 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOcoreSortTypeName =
                  ({-# LINE 243 "src/KnotSpec/Desugaring.ag" #-}
                   _lhsIcoreSortTypeName
                   {-# LINE 857 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 862 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 867 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 872 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 877 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 882 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 887 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 892 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 897 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 902 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOsortTypeName =
                  ({-# LINE 135 "src/KnotSpec/Environment.ag" #-}
                   _lhsIsortTypeName
                   {-# LINE 907 "src/KnotSpec/AG.hs" #-}
                   )
              ( _hdIdesugared,_hdInamespaceDependencies,_hdIsFunctionDef,_hdIself,_hdIsmeNamespaceCtor,_hdIsortDependencies) =
                  hd_ _hdOcoreSortTypeName _hdOmeEnvNameRoots _hdOmeEnvTypeName _hdOmeFunType _hdOmeNamespaceCtor _hdOmeNamespaceNameRoots _hdOmeNamespaceTypeName _hdOmeRelationEnv _hdOmeSortNameRoots _hdOmeSortTypeName _hdOsortTypeName
              ( _tlIdesugared,_tlInamespaceDependencies,_tlIsFunctionDef,_tlIself,_tlIsmeNamespaceCtor,_tlIsortDependencies) =
                  tl_ _tlOcoreSortTypeName _tlOmeEnvNameRoots _tlOmeEnvTypeName _tlOmeFunType _tlOmeNamespaceCtor _tlOmeNamespaceNameRoots _tlOmeNamespaceTypeName _tlOmeRelationEnv _tlOmeSortNameRoots _tlOmeSortTypeName _tlOsortTypeName
          in  ( _lhsOdesugared,_lhsOnamespaceDependencies,_lhsOsFunctionDef,_lhsOself,_lhsOsmeNamespaceCtor,_lhsOsortDependencies)))
sem_CtorDecls_Nil :: T_CtorDecls
sem_CtorDecls_Nil =
    (\ _lhsIcoreSortTypeName
       _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName
       _lhsIsortTypeName ->
         (let _lhsOdesugared :: (TcM [Core.CtorDecl])
              _lhsOnamespaceDependencies :: (TcM [Core.NamespaceTypeName])
              _lhsOsFunctionDef :: (TcM Core.FunctionEnv)
              _lhsOsmeNamespaceCtor :: MENamespaceCtor
              _lhsOsortDependencies :: (TcM [Core.SortTypeName])
              _lhsOself :: CtorDecls
              _lhsOdesugared =
                  ({-# LINE 172 "src/KnotSpec/Desugaring.ag" #-}
                   memptyA
                   {-# LINE 936 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOnamespaceDependencies =
                  ({-# LINE 483 "src/KnotSpec/Desugaring.ag" #-}
                   memptyA
                   {-# LINE 941 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOsFunctionDef =
                  ({-# LINE 603 "src/KnotSpec/Desugaring.ag" #-}
                   memptyA
                   {-# LINE 946 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOsmeNamespaceCtor =
                  ({-# LINE 143 "src/KnotSpec/Environment.ag" #-}
                   mempty
                   {-# LINE 951 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOsortDependencies =
                  ({-# LINE 480 "src/KnotSpec/Desugaring.ag" #-}
                   memptyA
                   {-# LINE 956 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  []
              _lhsOself =
                  _self
          in  ( _lhsOdesugared,_lhsOnamespaceDependencies,_lhsOsFunctionDef,_lhsOself,_lhsOsmeNamespaceCtor,_lhsOsortDependencies)))
-- EnvCtor -----------------------------------------------------
-- cata
sem_EnvCtor :: EnvCtor ->
               T_EnvCtor
sem_EnvCtor (EnvCtorNil _envCtorName) =
    (sem_EnvCtor_EnvCtorNil _envCtorName)
sem_EnvCtor (EnvCtorCons _envCtorName _envCtorMetavar _envCtorFields) =
    (sem_EnvCtor_EnvCtorCons _envCtorName (sem_Name _envCtorMetavar) (sem_Names _envCtorFields))
-- semantic domain
type T_EnvCtor = (Core.EnvVar) ->
                 (Core.EnvTypeName) ->
                 NameRoots ->
                 TypeName ->
                 MEEnvNameRoots ->
                 MEEnvTypeName ->
                 MEFunType ->
                 MENamespaceCtor ->
                 MENamespaceNameRoots ->
                 MENamespaceTypeName ->
                 MERelationEnv ->
                 MESortNameRoots ->
                 MESortTypeName ->
                 ( (TcM Core.EnvCtor),EnvCtor)
data Inh_EnvCtor = Inh_EnvCtor {coreEnvVar_Inh_EnvCtor :: (Core.EnvVar),coreTypeName_Inh_EnvCtor :: (Core.EnvTypeName),envNameRoots_Inh_EnvCtor :: NameRoots,envTypeName_Inh_EnvCtor :: TypeName,meEnvNameRoots_Inh_EnvCtor :: MEEnvNameRoots,meEnvTypeName_Inh_EnvCtor :: MEEnvTypeName,meFunType_Inh_EnvCtor :: MEFunType,meNamespaceCtor_Inh_EnvCtor :: MENamespaceCtor,meNamespaceNameRoots_Inh_EnvCtor :: MENamespaceNameRoots,meNamespaceTypeName_Inh_EnvCtor :: MENamespaceTypeName,meRelationEnv_Inh_EnvCtor :: MERelationEnv,meSortNameRoots_Inh_EnvCtor :: MESortNameRoots,meSortTypeName_Inh_EnvCtor :: MESortTypeName}
data Syn_EnvCtor = Syn_EnvCtor {desugared_Syn_EnvCtor :: (TcM Core.EnvCtor),self_Syn_EnvCtor :: EnvCtor}
wrap_EnvCtor :: T_EnvCtor ->
                Inh_EnvCtor ->
                Syn_EnvCtor
wrap_EnvCtor sem (Inh_EnvCtor _lhsIcoreEnvVar _lhsIcoreTypeName _lhsIenvNameRoots _lhsIenvTypeName _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName) =
    (let ( _lhsOdesugared,_lhsOself) = sem _lhsIcoreEnvVar _lhsIcoreTypeName _lhsIenvNameRoots _lhsIenvTypeName _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName
     in  (Syn_EnvCtor _lhsOdesugared _lhsOself))
sem_EnvCtor_EnvCtorNil :: CtorName ->
                          T_EnvCtor
sem_EnvCtor_EnvCtorNil envCtorName_ =
    (\ _lhsIcoreEnvVar
       _lhsIcoreTypeName
       _lhsIenvNameRoots
       _lhsIenvTypeName
       _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOself :: EnvCtor
              _lhsOdesugared :: (TcM Core.EnvCtor)
              _desugared =
                  ({-# LINE 335 "src/KnotSpec/Desugaring.ag" #-}
                   pure $ Core.EnvCtorNil (Core.CNE envCtorName_ _lhsIcoreTypeName)
                   {-# LINE 1015 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  EnvCtorNil envCtorName_
              _lhsOself =
                  _self
              _lhsOdesugared =
                  ({-# LINE 331 "src/KnotSpec/Desugaring.ag" #-}
                   _desugared
                   {-# LINE 1024 "src/KnotSpec/AG.hs" #-}
                   )
          in  ( _lhsOdesugared,_lhsOself)))
sem_EnvCtor_EnvCtorCons :: CtorName ->
                           T_Name ->
                           T_Names ->
                           T_EnvCtor
sem_EnvCtor_EnvCtorCons envCtorName_ envCtorMetavar_ envCtorFields_ =
    (\ _lhsIcoreEnvVar
       _lhsIcoreTypeName
       _lhsIenvNameRoots
       _lhsIenvTypeName
       _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOself :: EnvCtor
              _lhsOdesugared :: (TcM Core.EnvCtor)
              _envCtorMetavarOmeEnvNameRoots :: MEEnvNameRoots
              _envCtorMetavarOmeEnvTypeName :: MEEnvTypeName
              _envCtorMetavarOmeFunType :: MEFunType
              _envCtorMetavarOmeNamespaceCtor :: MENamespaceCtor
              _envCtorMetavarOmeNamespaceNameRoots :: MENamespaceNameRoots
              _envCtorMetavarOmeNamespaceTypeName :: MENamespaceTypeName
              _envCtorMetavarOmeRelationEnv :: MERelationEnv
              _envCtorMetavarOmeSortNameRoots :: MESortNameRoots
              _envCtorMetavarOmeSortTypeName :: MESortTypeName
              _envCtorFieldsOmeEnvNameRoots :: MEEnvNameRoots
              _envCtorFieldsOmeEnvTypeName :: MEEnvTypeName
              _envCtorFieldsOmeFunType :: MEFunType
              _envCtorFieldsOmeNamespaceCtor :: MENamespaceCtor
              _envCtorFieldsOmeNamespaceNameRoots :: MENamespaceNameRoots
              _envCtorFieldsOmeNamespaceTypeName :: MENamespaceTypeName
              _envCtorFieldsOmeRelationEnv :: MERelationEnv
              _envCtorFieldsOmeSortNameRoots :: MESortNameRoots
              _envCtorFieldsOmeSortTypeName :: MESortTypeName
              _envCtorMetavarIcoreFieldName :: (TcM CoreFieldName)
              _envCtorMetavarIcoreTypeName :: (TcM CoreTypeName)
              _envCtorMetavarIfieldMetaBinding :: (TcM Core.FieldMetaBinding)
              _envCtorMetavarImetavarName :: (TcM Core.MetavarVar)
              _envCtorMetavarInamespaceTypeName :: (TcM Core.NamespaceTypeName)
              _envCtorMetavarIroot :: NameRoot
              _envCtorMetavarIself :: Name
              _envCtorMetavarIsubtreeName :: (TcM Core.SubtreeVar)
              _envCtorMetavarIsuffix :: String
              _envCtorFieldsIfieldMetaBinding :: (TcM [Core.FieldMetaBinding])
              _envCtorFieldsIself :: Names
              _envCtorFieldsIsubtreeName :: (TcM [Core.SubtreeVar])
              _desugared =
                  ({-# LINE 338 "src/KnotSpec/Desugaring.ag" #-}
                   Core.EnvCtorCons (Core.CNE envCtorName_ _lhsIcoreTypeName)
                     <$> _envCtorMetavarImetavarName
                     <*> _envCtorFieldsIsubtreeName
                   {-# LINE 1082 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  EnvCtorCons envCtorName_ _envCtorMetavarIself _envCtorFieldsIself
              _lhsOself =
                  _self
              _lhsOdesugared =
                  ({-# LINE 331 "src/KnotSpec/Desugaring.ag" #-}
                   _desugared
                   {-# LINE 1091 "src/KnotSpec/AG.hs" #-}
                   )
              _envCtorMetavarOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 1096 "src/KnotSpec/AG.hs" #-}
                   )
              _envCtorMetavarOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 1101 "src/KnotSpec/AG.hs" #-}
                   )
              _envCtorMetavarOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 1106 "src/KnotSpec/AG.hs" #-}
                   )
              _envCtorMetavarOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 1111 "src/KnotSpec/AG.hs" #-}
                   )
              _envCtorMetavarOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 1116 "src/KnotSpec/AG.hs" #-}
                   )
              _envCtorMetavarOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 1121 "src/KnotSpec/AG.hs" #-}
                   )
              _envCtorMetavarOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 1126 "src/KnotSpec/AG.hs" #-}
                   )
              _envCtorMetavarOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 1131 "src/KnotSpec/AG.hs" #-}
                   )
              _envCtorMetavarOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 1136 "src/KnotSpec/AG.hs" #-}
                   )
              _envCtorFieldsOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 1141 "src/KnotSpec/AG.hs" #-}
                   )
              _envCtorFieldsOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 1146 "src/KnotSpec/AG.hs" #-}
                   )
              _envCtorFieldsOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 1151 "src/KnotSpec/AG.hs" #-}
                   )
              _envCtorFieldsOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 1156 "src/KnotSpec/AG.hs" #-}
                   )
              _envCtorFieldsOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 1161 "src/KnotSpec/AG.hs" #-}
                   )
              _envCtorFieldsOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 1166 "src/KnotSpec/AG.hs" #-}
                   )
              _envCtorFieldsOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 1171 "src/KnotSpec/AG.hs" #-}
                   )
              _envCtorFieldsOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 1176 "src/KnotSpec/AG.hs" #-}
                   )
              _envCtorFieldsOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 1181 "src/KnotSpec/AG.hs" #-}
                   )
              ( _envCtorMetavarIcoreFieldName,_envCtorMetavarIcoreTypeName,_envCtorMetavarIfieldMetaBinding,_envCtorMetavarImetavarName,_envCtorMetavarInamespaceTypeName,_envCtorMetavarIroot,_envCtorMetavarIself,_envCtorMetavarIsubtreeName,_envCtorMetavarIsuffix) =
                  envCtorMetavar_ _envCtorMetavarOmeEnvNameRoots _envCtorMetavarOmeEnvTypeName _envCtorMetavarOmeFunType _envCtorMetavarOmeNamespaceCtor _envCtorMetavarOmeNamespaceNameRoots _envCtorMetavarOmeNamespaceTypeName _envCtorMetavarOmeRelationEnv _envCtorMetavarOmeSortNameRoots _envCtorMetavarOmeSortTypeName
              ( _envCtorFieldsIfieldMetaBinding,_envCtorFieldsIself,_envCtorFieldsIsubtreeName) =
                  envCtorFields_ _envCtorFieldsOmeEnvNameRoots _envCtorFieldsOmeEnvTypeName _envCtorFieldsOmeFunType _envCtorFieldsOmeNamespaceCtor _envCtorFieldsOmeNamespaceNameRoots _envCtorFieldsOmeNamespaceTypeName _envCtorFieldsOmeRelationEnv _envCtorFieldsOmeSortNameRoots _envCtorFieldsOmeSortTypeName
          in  ( _lhsOdesugared,_lhsOself)))
-- EnvCtors ----------------------------------------------------
-- cata
sem_EnvCtors :: EnvCtors ->
                T_EnvCtors
sem_EnvCtors list =
    (Prelude.foldr sem_EnvCtors_Cons sem_EnvCtors_Nil (Prelude.map sem_EnvCtor list))
-- semantic domain
type T_EnvCtors = (Core.EnvVar) ->
                  (Core.EnvTypeName) ->
                  NameRoots ->
                  TypeName ->
                  MEEnvNameRoots ->
                  MEEnvTypeName ->
                  MEFunType ->
                  MENamespaceCtor ->
                  MENamespaceNameRoots ->
                  MENamespaceTypeName ->
                  MERelationEnv ->
                  MESortNameRoots ->
                  MESortTypeName ->
                  ( (TcM [Core.EnvCtor]),EnvCtors)
data Inh_EnvCtors = Inh_EnvCtors {coreEnvVar_Inh_EnvCtors :: (Core.EnvVar),coreTypeName_Inh_EnvCtors :: (Core.EnvTypeName),envNameRoots_Inh_EnvCtors :: NameRoots,envTypeName_Inh_EnvCtors :: TypeName,meEnvNameRoots_Inh_EnvCtors :: MEEnvNameRoots,meEnvTypeName_Inh_EnvCtors :: MEEnvTypeName,meFunType_Inh_EnvCtors :: MEFunType,meNamespaceCtor_Inh_EnvCtors :: MENamespaceCtor,meNamespaceNameRoots_Inh_EnvCtors :: MENamespaceNameRoots,meNamespaceTypeName_Inh_EnvCtors :: MENamespaceTypeName,meRelationEnv_Inh_EnvCtors :: MERelationEnv,meSortNameRoots_Inh_EnvCtors :: MESortNameRoots,meSortTypeName_Inh_EnvCtors :: MESortTypeName}
data Syn_EnvCtors = Syn_EnvCtors {desugared_Syn_EnvCtors :: (TcM [Core.EnvCtor]),self_Syn_EnvCtors :: EnvCtors}
wrap_EnvCtors :: T_EnvCtors ->
                 Inh_EnvCtors ->
                 Syn_EnvCtors
wrap_EnvCtors sem (Inh_EnvCtors _lhsIcoreEnvVar _lhsIcoreTypeName _lhsIenvNameRoots _lhsIenvTypeName _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName) =
    (let ( _lhsOdesugared,_lhsOself) = sem _lhsIcoreEnvVar _lhsIcoreTypeName _lhsIenvNameRoots _lhsIenvTypeName _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName
     in  (Syn_EnvCtors _lhsOdesugared _lhsOself))
sem_EnvCtors_Cons :: T_EnvCtor ->
                     T_EnvCtors ->
                     T_EnvCtors
sem_EnvCtors_Cons hd_ tl_ =
    (\ _lhsIcoreEnvVar
       _lhsIcoreTypeName
       _lhsIenvNameRoots
       _lhsIenvTypeName
       _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOdesugared :: (TcM [Core.EnvCtor])
              _lhsOself :: EnvCtors
              _hdOcoreEnvVar :: (Core.EnvVar)
              _hdOcoreTypeName :: (Core.EnvTypeName)
              _hdOenvNameRoots :: NameRoots
              _hdOenvTypeName :: TypeName
              _hdOmeEnvNameRoots :: MEEnvNameRoots
              _hdOmeEnvTypeName :: MEEnvTypeName
              _hdOmeFunType :: MEFunType
              _hdOmeNamespaceCtor :: MENamespaceCtor
              _hdOmeNamespaceNameRoots :: MENamespaceNameRoots
              _hdOmeNamespaceTypeName :: MENamespaceTypeName
              _hdOmeRelationEnv :: MERelationEnv
              _hdOmeSortNameRoots :: MESortNameRoots
              _hdOmeSortTypeName :: MESortTypeName
              _tlOcoreEnvVar :: (Core.EnvVar)
              _tlOcoreTypeName :: (Core.EnvTypeName)
              _tlOenvNameRoots :: NameRoots
              _tlOenvTypeName :: TypeName
              _tlOmeEnvNameRoots :: MEEnvNameRoots
              _tlOmeEnvTypeName :: MEEnvTypeName
              _tlOmeFunType :: MEFunType
              _tlOmeNamespaceCtor :: MENamespaceCtor
              _tlOmeNamespaceNameRoots :: MENamespaceNameRoots
              _tlOmeNamespaceTypeName :: MENamespaceTypeName
              _tlOmeRelationEnv :: MERelationEnv
              _tlOmeSortNameRoots :: MESortNameRoots
              _tlOmeSortTypeName :: MESortTypeName
              _hdIdesugared :: (TcM Core.EnvCtor)
              _hdIself :: EnvCtor
              _tlIdesugared :: (TcM [Core.EnvCtor])
              _tlIself :: EnvCtors
              _lhsOdesugared =
                  ({-# LINE 330 "src/KnotSpec/Desugaring.ag" #-}
                   (consA _hdIdesugared _tlIdesugared)
                   {-# LINE 1269 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _hdOcoreEnvVar =
                  ({-# LINE 315 "src/KnotSpec/Desugaring.ag" #-}
                   _lhsIcoreEnvVar
                   {-# LINE 1278 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOcoreTypeName =
                  ({-# LINE 314 "src/KnotSpec/Desugaring.ag" #-}
                   _lhsIcoreTypeName
                   {-# LINE 1283 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOenvNameRoots =
                  ({-# LINE 205 "src/KnotSpec/Environment.ag" #-}
                   _lhsIenvNameRoots
                   {-# LINE 1288 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOenvTypeName =
                  ({-# LINE 204 "src/KnotSpec/Environment.ag" #-}
                   _lhsIenvTypeName
                   {-# LINE 1293 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 1298 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 1303 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 1308 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 1313 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 1318 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 1323 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 1328 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 1333 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 1338 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOcoreEnvVar =
                  ({-# LINE 315 "src/KnotSpec/Desugaring.ag" #-}
                   _lhsIcoreEnvVar
                   {-# LINE 1343 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOcoreTypeName =
                  ({-# LINE 314 "src/KnotSpec/Desugaring.ag" #-}
                   _lhsIcoreTypeName
                   {-# LINE 1348 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOenvNameRoots =
                  ({-# LINE 205 "src/KnotSpec/Environment.ag" #-}
                   _lhsIenvNameRoots
                   {-# LINE 1353 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOenvTypeName =
                  ({-# LINE 204 "src/KnotSpec/Environment.ag" #-}
                   _lhsIenvTypeName
                   {-# LINE 1358 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 1363 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 1368 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 1373 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 1378 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 1383 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 1388 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 1393 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 1398 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 1403 "src/KnotSpec/AG.hs" #-}
                   )
              ( _hdIdesugared,_hdIself) =
                  hd_ _hdOcoreEnvVar _hdOcoreTypeName _hdOenvNameRoots _hdOenvTypeName _hdOmeEnvNameRoots _hdOmeEnvTypeName _hdOmeFunType _hdOmeNamespaceCtor _hdOmeNamespaceNameRoots _hdOmeNamespaceTypeName _hdOmeRelationEnv _hdOmeSortNameRoots _hdOmeSortTypeName
              ( _tlIdesugared,_tlIself) =
                  tl_ _tlOcoreEnvVar _tlOcoreTypeName _tlOenvNameRoots _tlOenvTypeName _tlOmeEnvNameRoots _tlOmeEnvTypeName _tlOmeFunType _tlOmeNamespaceCtor _tlOmeNamespaceNameRoots _tlOmeNamespaceTypeName _tlOmeRelationEnv _tlOmeSortNameRoots _tlOmeSortTypeName
          in  ( _lhsOdesugared,_lhsOself)))
sem_EnvCtors_Nil :: T_EnvCtors
sem_EnvCtors_Nil =
    (\ _lhsIcoreEnvVar
       _lhsIcoreTypeName
       _lhsIenvNameRoots
       _lhsIenvTypeName
       _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOdesugared :: (TcM [Core.EnvCtor])
              _lhsOself :: EnvCtors
              _lhsOdesugared =
                  ({-# LINE 330 "src/KnotSpec/Desugaring.ag" #-}
                   memptyA
                   {-# LINE 1430 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  []
              _lhsOself =
                  _self
          in  ( _lhsOdesugared,_lhsOself)))
-- EnvDecl -----------------------------------------------------
-- cata
sem_EnvDecl :: EnvDecl ->
               T_EnvDecl
sem_EnvDecl (EnvDecl _envTypeName _envNameRoots _envCtors) =
    (sem_EnvDecl_EnvDecl (sem_TypeName _envTypeName) (sem_NameRoots _envNameRoots) (sem_EnvCtors _envCtors))
-- semantic domain
type T_EnvDecl = MEEnvNameRoots ->
                 MEEnvTypeName ->
                 MEFunType ->
                 MENamespaceCtor ->
                 MENamespaceNameRoots ->
                 MENamespaceTypeName ->
                 MERelationEnv ->
                 MESortNameRoots ->
                 MESortTypeName ->
                 ( (TcM Core.EnvDecl),EnvDecl,MEEnvNameRoots)
data Inh_EnvDecl = Inh_EnvDecl {meEnvNameRoots_Inh_EnvDecl :: MEEnvNameRoots,meEnvTypeName_Inh_EnvDecl :: MEEnvTypeName,meFunType_Inh_EnvDecl :: MEFunType,meNamespaceCtor_Inh_EnvDecl :: MENamespaceCtor,meNamespaceNameRoots_Inh_EnvDecl :: MENamespaceNameRoots,meNamespaceTypeName_Inh_EnvDecl :: MENamespaceTypeName,meRelationEnv_Inh_EnvDecl :: MERelationEnv,meSortNameRoots_Inh_EnvDecl :: MESortNameRoots,meSortTypeName_Inh_EnvDecl :: MESortTypeName}
data Syn_EnvDecl = Syn_EnvDecl {desugared_Syn_EnvDecl :: (TcM Core.EnvDecl),self_Syn_EnvDecl :: EnvDecl,smeEnvNameRoots_Syn_EnvDecl :: MEEnvNameRoots}
wrap_EnvDecl :: T_EnvDecl ->
                Inh_EnvDecl ->
                Syn_EnvDecl
wrap_EnvDecl sem (Inh_EnvDecl _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName) =
    (let ( _lhsOdesugared,_lhsOself,_lhsOsmeEnvNameRoots) = sem _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName
     in  (Syn_EnvDecl _lhsOdesugared _lhsOself _lhsOsmeEnvNameRoots))
sem_EnvDecl_EnvDecl :: T_TypeName ->
                       T_NameRoots ->
                       T_EnvCtors ->
                       T_EnvDecl
sem_EnvDecl_EnvDecl envTypeName_ envNameRoots_ envCtors_ =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOsmeEnvNameRoots :: MEEnvNameRoots
              _lhsOself :: EnvDecl
              _lhsOdesugared :: (TcM Core.EnvDecl)
              _envTypeNameOmeEnvNameRoots :: MEEnvNameRoots
              _envTypeNameOmeEnvTypeName :: MEEnvTypeName
              _envTypeNameOmeFunType :: MEFunType
              _envTypeNameOmeNamespaceCtor :: MENamespaceCtor
              _envTypeNameOmeNamespaceNameRoots :: MENamespaceNameRoots
              _envTypeNameOmeNamespaceTypeName :: MENamespaceTypeName
              _envTypeNameOmeRelationEnv :: MERelationEnv
              _envTypeNameOmeSortNameRoots :: MESortNameRoots
              _envTypeNameOmeSortTypeName :: MESortTypeName
              _envCtorsOcoreEnvVar :: (Core.EnvVar)
              _envCtorsOcoreTypeName :: (Core.EnvTypeName)
              _envCtorsOenvNameRoots :: NameRoots
              _envCtorsOenvTypeName :: TypeName
              _envCtorsOmeEnvNameRoots :: MEEnvNameRoots
              _envCtorsOmeEnvTypeName :: MEEnvTypeName
              _envCtorsOmeFunType :: MEFunType
              _envCtorsOmeNamespaceCtor :: MENamespaceCtor
              _envCtorsOmeNamespaceNameRoots :: MENamespaceNameRoots
              _envCtorsOmeNamespaceTypeName :: MENamespaceTypeName
              _envCtorsOmeRelationEnv :: MERelationEnv
              _envCtorsOmeSortNameRoots :: MESortNameRoots
              _envCtorsOmeSortTypeName :: MESortTypeName
              _envTypeNameIfromTn :: String
              _envTypeNameInamespaceTypeName :: (TcM Core.NamespaceTypeName)
              _envTypeNameIrelationTypeName :: (TcM Core.RelationTypeName)
              _envTypeNameIself :: TypeName
              _envTypeNameIsortTypeName :: (TcM Core.SortTypeName)
              _envNameRootsIself :: NameRoots
              _envCtorsIdesugared :: (TcM [Core.EnvCtor])
              _envCtorsIself :: EnvCtors
              _coreNameRoots =
                  ({-# LINE 319 "src/KnotSpec/Desugaring.ag" #-}
                   map (Core.NR . fromNR) _envNameRootsIself
                   {-# LINE 1512 "src/KnotSpec/AG.hs" #-}
                   )
              _coreTypeName =
                  ({-# LINE 320 "src/KnotSpec/Desugaring.ag" #-}
                   Core.ETN _envTypeNameIfromTn
                   {-# LINE 1517 "src/KnotSpec/AG.hs" #-}
                   )
              _coreEnvVar =
                  ({-# LINE 321 "src/KnotSpec/Desugaring.ag" #-}
                   Core.EnvVar
                     (head _coreNameRoots    )
                     ""
                     (_coreTypeName    )
                   {-# LINE 1525 "src/KnotSpec/AG.hs" #-}
                   )
              _desugared =
                  ({-# LINE 326 "src/KnotSpec/Desugaring.ag" #-}
                   Core.EnvDecl _coreTypeName     _coreNameRoots
                     <$> _envCtorsIdesugared
                   {-# LINE 1531 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOsmeEnvNameRoots =
                  ({-# LINE 209 "src/KnotSpec/Environment.ag" #-}
                   Data.Map.singleton _envTypeNameIself _envNameRootsIself
                   {-# LINE 1536 "src/KnotSpec/AG.hs" #-}
                   )
              _envTypeName =
                  ({-# LINE 210 "src/KnotSpec/Environment.ag" #-}
                   _envTypeNameIself
                   {-# LINE 1541 "src/KnotSpec/AG.hs" #-}
                   )
              _envNameRoots =
                  ({-# LINE 211 "src/KnotSpec/Environment.ag" #-}
                   _envNameRootsIself
                   {-# LINE 1546 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  EnvDecl _envTypeNameIself _envNameRootsIself _envCtorsIself
              _lhsOself =
                  _self
              _lhsOdesugared =
                  ({-# LINE 311 "src/KnotSpec/Desugaring.ag" #-}
                   _desugared
                   {-# LINE 1555 "src/KnotSpec/AG.hs" #-}
                   )
              _envTypeNameOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 1560 "src/KnotSpec/AG.hs" #-}
                   )
              _envTypeNameOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 1565 "src/KnotSpec/AG.hs" #-}
                   )
              _envTypeNameOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 1570 "src/KnotSpec/AG.hs" #-}
                   )
              _envTypeNameOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 1575 "src/KnotSpec/AG.hs" #-}
                   )
              _envTypeNameOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 1580 "src/KnotSpec/AG.hs" #-}
                   )
              _envTypeNameOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 1585 "src/KnotSpec/AG.hs" #-}
                   )
              _envTypeNameOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 1590 "src/KnotSpec/AG.hs" #-}
                   )
              _envTypeNameOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 1595 "src/KnotSpec/AG.hs" #-}
                   )
              _envTypeNameOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 1600 "src/KnotSpec/AG.hs" #-}
                   )
              _envCtorsOcoreEnvVar =
                  ({-# LINE 315 "src/KnotSpec/Desugaring.ag" #-}
                   _coreEnvVar
                   {-# LINE 1605 "src/KnotSpec/AG.hs" #-}
                   )
              _envCtorsOcoreTypeName =
                  ({-# LINE 314 "src/KnotSpec/Desugaring.ag" #-}
                   _coreTypeName
                   {-# LINE 1610 "src/KnotSpec/AG.hs" #-}
                   )
              _envCtorsOenvNameRoots =
                  ({-# LINE 205 "src/KnotSpec/Environment.ag" #-}
                   _envNameRoots
                   {-# LINE 1615 "src/KnotSpec/AG.hs" #-}
                   )
              _envCtorsOenvTypeName =
                  ({-# LINE 204 "src/KnotSpec/Environment.ag" #-}
                   _envTypeName
                   {-# LINE 1620 "src/KnotSpec/AG.hs" #-}
                   )
              _envCtorsOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 1625 "src/KnotSpec/AG.hs" #-}
                   )
              _envCtorsOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 1630 "src/KnotSpec/AG.hs" #-}
                   )
              _envCtorsOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 1635 "src/KnotSpec/AG.hs" #-}
                   )
              _envCtorsOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 1640 "src/KnotSpec/AG.hs" #-}
                   )
              _envCtorsOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 1645 "src/KnotSpec/AG.hs" #-}
                   )
              _envCtorsOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 1650 "src/KnotSpec/AG.hs" #-}
                   )
              _envCtorsOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 1655 "src/KnotSpec/AG.hs" #-}
                   )
              _envCtorsOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 1660 "src/KnotSpec/AG.hs" #-}
                   )
              _envCtorsOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 1665 "src/KnotSpec/AG.hs" #-}
                   )
              ( _envTypeNameIfromTn,_envTypeNameInamespaceTypeName,_envTypeNameIrelationTypeName,_envTypeNameIself,_envTypeNameIsortTypeName) =
                  envTypeName_ _envTypeNameOmeEnvNameRoots _envTypeNameOmeEnvTypeName _envTypeNameOmeFunType _envTypeNameOmeNamespaceCtor _envTypeNameOmeNamespaceNameRoots _envTypeNameOmeNamespaceTypeName _envTypeNameOmeRelationEnv _envTypeNameOmeSortNameRoots _envTypeNameOmeSortTypeName
              ( _envNameRootsIself) =
                  envNameRoots_
              ( _envCtorsIdesugared,_envCtorsIself) =
                  envCtors_ _envCtorsOcoreEnvVar _envCtorsOcoreTypeName _envCtorsOenvNameRoots _envCtorsOenvTypeName _envCtorsOmeEnvNameRoots _envCtorsOmeEnvTypeName _envCtorsOmeFunType _envCtorsOmeNamespaceCtor _envCtorsOmeNamespaceNameRoots _envCtorsOmeNamespaceTypeName _envCtorsOmeRelationEnv _envCtorsOmeSortNameRoots _envCtorsOmeSortTypeName
          in  ( _lhsOdesugared,_lhsOself,_lhsOsmeEnvNameRoots)))
-- EnvDecls ----------------------------------------------------
-- cata
sem_EnvDecls :: EnvDecls ->
                T_EnvDecls
sem_EnvDecls list =
    (Prelude.foldr sem_EnvDecls_Cons sem_EnvDecls_Nil (Prelude.map sem_EnvDecl list))
-- semantic domain
type T_EnvDecls = MEEnvNameRoots ->
                  MEEnvTypeName ->
                  MEFunType ->
                  MENamespaceCtor ->
                  MENamespaceNameRoots ->
                  MENamespaceTypeName ->
                  MERelationEnv ->
                  MESortNameRoots ->
                  MESortTypeName ->
                  ( (TcM [Core.EnvDecl]),EnvDecls,MEEnvNameRoots)
data Inh_EnvDecls = Inh_EnvDecls {meEnvNameRoots_Inh_EnvDecls :: MEEnvNameRoots,meEnvTypeName_Inh_EnvDecls :: MEEnvTypeName,meFunType_Inh_EnvDecls :: MEFunType,meNamespaceCtor_Inh_EnvDecls :: MENamespaceCtor,meNamespaceNameRoots_Inh_EnvDecls :: MENamespaceNameRoots,meNamespaceTypeName_Inh_EnvDecls :: MENamespaceTypeName,meRelationEnv_Inh_EnvDecls :: MERelationEnv,meSortNameRoots_Inh_EnvDecls :: MESortNameRoots,meSortTypeName_Inh_EnvDecls :: MESortTypeName}
data Syn_EnvDecls = Syn_EnvDecls {desugared_Syn_EnvDecls :: (TcM [Core.EnvDecl]),self_Syn_EnvDecls :: EnvDecls,smeEnvNameRoots_Syn_EnvDecls :: MEEnvNameRoots}
wrap_EnvDecls :: T_EnvDecls ->
                 Inh_EnvDecls ->
                 Syn_EnvDecls
wrap_EnvDecls sem (Inh_EnvDecls _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName) =
    (let ( _lhsOdesugared,_lhsOself,_lhsOsmeEnvNameRoots) = sem _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName
     in  (Syn_EnvDecls _lhsOdesugared _lhsOself _lhsOsmeEnvNameRoots))
sem_EnvDecls_Cons :: T_EnvDecl ->
                     T_EnvDecls ->
                     T_EnvDecls
sem_EnvDecls_Cons hd_ tl_ =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOdesugared :: (TcM [Core.EnvDecl])
              _lhsOsmeEnvNameRoots :: MEEnvNameRoots
              _lhsOself :: EnvDecls
              _hdOmeEnvNameRoots :: MEEnvNameRoots
              _hdOmeEnvTypeName :: MEEnvTypeName
              _hdOmeFunType :: MEFunType
              _hdOmeNamespaceCtor :: MENamespaceCtor
              _hdOmeNamespaceNameRoots :: MENamespaceNameRoots
              _hdOmeNamespaceTypeName :: MENamespaceTypeName
              _hdOmeRelationEnv :: MERelationEnv
              _hdOmeSortNameRoots :: MESortNameRoots
              _hdOmeSortTypeName :: MESortTypeName
              _tlOmeEnvNameRoots :: MEEnvNameRoots
              _tlOmeEnvTypeName :: MEEnvTypeName
              _tlOmeFunType :: MEFunType
              _tlOmeNamespaceCtor :: MENamespaceCtor
              _tlOmeNamespaceNameRoots :: MENamespaceNameRoots
              _tlOmeNamespaceTypeName :: MENamespaceTypeName
              _tlOmeRelationEnv :: MERelationEnv
              _tlOmeSortNameRoots :: MESortNameRoots
              _tlOmeSortTypeName :: MESortTypeName
              _hdIdesugared :: (TcM Core.EnvDecl)
              _hdIself :: EnvDecl
              _hdIsmeEnvNameRoots :: MEEnvNameRoots
              _tlIdesugared :: (TcM [Core.EnvDecl])
              _tlIself :: EnvDecls
              _tlIsmeEnvNameRoots :: MEEnvNameRoots
              _lhsOdesugared =
                  ({-# LINE 310 "src/KnotSpec/Desugaring.ag" #-}
                   (consA _hdIdesugared _tlIdesugared)
                   {-# LINE 1742 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOsmeEnvNameRoots =
                  ({-# LINE 195 "src/KnotSpec/Environment.ag" #-}
                   (Data.Map.unionWith (error "smeEnvNameRoots union") _hdIsmeEnvNameRoots _tlIsmeEnvNameRoots)
                   {-# LINE 1747 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _hdOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 1756 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 1761 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 1766 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 1771 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 1776 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 1781 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 1786 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 1791 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 1796 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 1801 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 1806 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 1811 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 1816 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 1821 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 1826 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 1831 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 1836 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 1841 "src/KnotSpec/AG.hs" #-}
                   )
              ( _hdIdesugared,_hdIself,_hdIsmeEnvNameRoots) =
                  hd_ _hdOmeEnvNameRoots _hdOmeEnvTypeName _hdOmeFunType _hdOmeNamespaceCtor _hdOmeNamespaceNameRoots _hdOmeNamespaceTypeName _hdOmeRelationEnv _hdOmeSortNameRoots _hdOmeSortTypeName
              ( _tlIdesugared,_tlIself,_tlIsmeEnvNameRoots) =
                  tl_ _tlOmeEnvNameRoots _tlOmeEnvTypeName _tlOmeFunType _tlOmeNamespaceCtor _tlOmeNamespaceNameRoots _tlOmeNamespaceTypeName _tlOmeRelationEnv _tlOmeSortNameRoots _tlOmeSortTypeName
          in  ( _lhsOdesugared,_lhsOself,_lhsOsmeEnvNameRoots)))
sem_EnvDecls_Nil :: T_EnvDecls
sem_EnvDecls_Nil =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOdesugared :: (TcM [Core.EnvDecl])
              _lhsOsmeEnvNameRoots :: MEEnvNameRoots
              _lhsOself :: EnvDecls
              _lhsOdesugared =
                  ({-# LINE 310 "src/KnotSpec/Desugaring.ag" #-}
                   memptyA
                   {-# LINE 1865 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOsmeEnvNameRoots =
                  ({-# LINE 195 "src/KnotSpec/Environment.ag" #-}
                   mempty
                   {-# LINE 1870 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  []
              _lhsOself =
                  _self
          in  ( _lhsOdesugared,_lhsOself,_lhsOsmeEnvNameRoots)))
-- FieldDecl ---------------------------------------------------
-- cata
sem_FieldDecl :: FieldDecl ->
                 T_FieldDecl
sem_FieldDecl (FieldDecl _fieldBindSpec _fieldName) =
    (sem_FieldDecl_FieldDecl (sem_BindSpec _fieldBindSpec) (sem_Name _fieldName))
-- semantic domain
type T_FieldDecl = MEEnvNameRoots ->
                   MEEnvTypeName ->
                   MEFunType ->
                   MENamespaceCtor ->
                   MENamespaceNameRoots ->
                   MENamespaceTypeName ->
                   MERelationEnv ->
                   MESortNameRoots ->
                   MESortTypeName ->
                   ( (TcM Core.FieldDecl),(TcM [Core.NamespaceTypeName]),FieldDecl,(TcM [Core.SortTypeName]))
data Inh_FieldDecl = Inh_FieldDecl {meEnvNameRoots_Inh_FieldDecl :: MEEnvNameRoots,meEnvTypeName_Inh_FieldDecl :: MEEnvTypeName,meFunType_Inh_FieldDecl :: MEFunType,meNamespaceCtor_Inh_FieldDecl :: MENamespaceCtor,meNamespaceNameRoots_Inh_FieldDecl :: MENamespaceNameRoots,meNamespaceTypeName_Inh_FieldDecl :: MENamespaceTypeName,meRelationEnv_Inh_FieldDecl :: MERelationEnv,meSortNameRoots_Inh_FieldDecl :: MESortNameRoots,meSortTypeName_Inh_FieldDecl :: MESortTypeName}
data Syn_FieldDecl = Syn_FieldDecl {desugared_Syn_FieldDecl :: (TcM Core.FieldDecl),namespaceDependencies_Syn_FieldDecl :: (TcM [Core.NamespaceTypeName]),self_Syn_FieldDecl :: FieldDecl,sortDependencies_Syn_FieldDecl :: (TcM [Core.SortTypeName])}
wrap_FieldDecl :: T_FieldDecl ->
                  Inh_FieldDecl ->
                  Syn_FieldDecl
wrap_FieldDecl sem (Inh_FieldDecl _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName) =
    (let ( _lhsOdesugared,_lhsOnamespaceDependencies,_lhsOself,_lhsOsortDependencies) = sem _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName
     in  (Syn_FieldDecl _lhsOdesugared _lhsOnamespaceDependencies _lhsOself _lhsOsortDependencies))
sem_FieldDecl_FieldDecl :: T_BindSpec ->
                           T_Name ->
                           T_FieldDecl
sem_FieldDecl_FieldDecl fieldBindSpec_ fieldName_ =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOsortDependencies :: (TcM [Core.SortTypeName])
              _lhsOnamespaceDependencies :: (TcM [Core.NamespaceTypeName])
              _lhsOself :: FieldDecl
              _lhsOdesugared :: (TcM Core.FieldDecl)
              _fieldBindSpecOmeEnvNameRoots :: MEEnvNameRoots
              _fieldBindSpecOmeEnvTypeName :: MEEnvTypeName
              _fieldBindSpecOmeFunType :: MEFunType
              _fieldBindSpecOmeNamespaceCtor :: MENamespaceCtor
              _fieldBindSpecOmeNamespaceNameRoots :: MENamespaceNameRoots
              _fieldBindSpecOmeNamespaceTypeName :: MENamespaceTypeName
              _fieldBindSpecOmeRelationEnv :: MERelationEnv
              _fieldBindSpecOmeSortNameRoots :: MESortNameRoots
              _fieldBindSpecOmeSortTypeName :: MESortTypeName
              _fieldNameOmeEnvNameRoots :: MEEnvNameRoots
              _fieldNameOmeEnvTypeName :: MEEnvTypeName
              _fieldNameOmeFunType :: MEFunType
              _fieldNameOmeNamespaceCtor :: MENamespaceCtor
              _fieldNameOmeNamespaceNameRoots :: MENamespaceNameRoots
              _fieldNameOmeNamespaceTypeName :: MENamespaceTypeName
              _fieldNameOmeRelationEnv :: MERelationEnv
              _fieldNameOmeSortNameRoots :: MESortNameRoots
              _fieldNameOmeSortTypeName :: MESortTypeName
              _fieldBindSpecIdesugared :: (TcM Core.BindSpec)
              _fieldBindSpecIself :: BindSpec
              _fieldNameIcoreFieldName :: (TcM CoreFieldName)
              _fieldNameIcoreTypeName :: (TcM CoreTypeName)
              _fieldNameIfieldMetaBinding :: (TcM Core.FieldMetaBinding)
              _fieldNameImetavarName :: (TcM Core.MetavarVar)
              _fieldNameInamespaceTypeName :: (TcM Core.NamespaceTypeName)
              _fieldNameIroot :: NameRoot
              _fieldNameIself :: Name
              _fieldNameIsubtreeName :: (TcM Core.SubtreeVar)
              _fieldNameIsuffix :: String
              _desugared =
                  ({-# LINE 263 "src/KnotSpec/Desugaring.ag" #-}
                   do
                     coreFieldName <- _fieldNameIcoreFieldName
                     case coreFieldName of
                       FRS subtreeName ->
                         Core.FieldSubtree subtreeName <$> _fieldBindSpecIdesugared
                       FRN metavarName ->
                         if null _fieldBindSpecIself
                           then return (Core.FieldBinding metavarName)
                           else throwError "Invalid binding specification for variable field"
                   {-# LINE 1959 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOsortDependencies =
                  ({-# LINE 498 "src/KnotSpec/Desugaring.ag" #-}
                   do
                     coreTypeName <- _fieldNameIcoreTypeName
                     case coreTypeName of
                       STN stn -> return [stn]
                       _       -> return []
                   {-# LINE 1968 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOnamespaceDependencies =
                  ({-# LINE 504 "src/KnotSpec/Desugaring.ag" #-}
                   return []
                   {-# LINE 1973 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  FieldDecl _fieldBindSpecIself _fieldNameIself
              _lhsOself =
                  _self
              _lhsOdesugared =
                  ({-# LINE 175 "src/KnotSpec/Desugaring.ag" #-}
                   _desugared
                   {-# LINE 1982 "src/KnotSpec/AG.hs" #-}
                   )
              _fieldBindSpecOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 1987 "src/KnotSpec/AG.hs" #-}
                   )
              _fieldBindSpecOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 1992 "src/KnotSpec/AG.hs" #-}
                   )
              _fieldBindSpecOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 1997 "src/KnotSpec/AG.hs" #-}
                   )
              _fieldBindSpecOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 2002 "src/KnotSpec/AG.hs" #-}
                   )
              _fieldBindSpecOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 2007 "src/KnotSpec/AG.hs" #-}
                   )
              _fieldBindSpecOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 2012 "src/KnotSpec/AG.hs" #-}
                   )
              _fieldBindSpecOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 2017 "src/KnotSpec/AG.hs" #-}
                   )
              _fieldBindSpecOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 2022 "src/KnotSpec/AG.hs" #-}
                   )
              _fieldBindSpecOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 2027 "src/KnotSpec/AG.hs" #-}
                   )
              _fieldNameOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 2032 "src/KnotSpec/AG.hs" #-}
                   )
              _fieldNameOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 2037 "src/KnotSpec/AG.hs" #-}
                   )
              _fieldNameOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 2042 "src/KnotSpec/AG.hs" #-}
                   )
              _fieldNameOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 2047 "src/KnotSpec/AG.hs" #-}
                   )
              _fieldNameOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 2052 "src/KnotSpec/AG.hs" #-}
                   )
              _fieldNameOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 2057 "src/KnotSpec/AG.hs" #-}
                   )
              _fieldNameOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 2062 "src/KnotSpec/AG.hs" #-}
                   )
              _fieldNameOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 2067 "src/KnotSpec/AG.hs" #-}
                   )
              _fieldNameOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 2072 "src/KnotSpec/AG.hs" #-}
                   )
              ( _fieldBindSpecIdesugared,_fieldBindSpecIself) =
                  fieldBindSpec_ _fieldBindSpecOmeEnvNameRoots _fieldBindSpecOmeEnvTypeName _fieldBindSpecOmeFunType _fieldBindSpecOmeNamespaceCtor _fieldBindSpecOmeNamespaceNameRoots _fieldBindSpecOmeNamespaceTypeName _fieldBindSpecOmeRelationEnv _fieldBindSpecOmeSortNameRoots _fieldBindSpecOmeSortTypeName
              ( _fieldNameIcoreFieldName,_fieldNameIcoreTypeName,_fieldNameIfieldMetaBinding,_fieldNameImetavarName,_fieldNameInamespaceTypeName,_fieldNameIroot,_fieldNameIself,_fieldNameIsubtreeName,_fieldNameIsuffix) =
                  fieldName_ _fieldNameOmeEnvNameRoots _fieldNameOmeEnvTypeName _fieldNameOmeFunType _fieldNameOmeNamespaceCtor _fieldNameOmeNamespaceNameRoots _fieldNameOmeNamespaceTypeName _fieldNameOmeRelationEnv _fieldNameOmeSortNameRoots _fieldNameOmeSortTypeName
          in  ( _lhsOdesugared,_lhsOnamespaceDependencies,_lhsOself,_lhsOsortDependencies)))
-- FieldDecls --------------------------------------------------
-- cata
sem_FieldDecls :: FieldDecls ->
                  T_FieldDecls
sem_FieldDecls list =
    (Prelude.foldr sem_FieldDecls_Cons sem_FieldDecls_Nil (Prelude.map sem_FieldDecl list))
-- semantic domain
type T_FieldDecls = MEEnvNameRoots ->
                    MEEnvTypeName ->
                    MEFunType ->
                    MENamespaceCtor ->
                    MENamespaceNameRoots ->
                    MENamespaceTypeName ->
                    MERelationEnv ->
                    MESortNameRoots ->
                    MESortTypeName ->
                    ( (TcM [Core.FieldDecl]),(TcM [Core.NamespaceTypeName]),FieldDecls,(TcM [Core.SortTypeName]))
data Inh_FieldDecls = Inh_FieldDecls {meEnvNameRoots_Inh_FieldDecls :: MEEnvNameRoots,meEnvTypeName_Inh_FieldDecls :: MEEnvTypeName,meFunType_Inh_FieldDecls :: MEFunType,meNamespaceCtor_Inh_FieldDecls :: MENamespaceCtor,meNamespaceNameRoots_Inh_FieldDecls :: MENamespaceNameRoots,meNamespaceTypeName_Inh_FieldDecls :: MENamespaceTypeName,meRelationEnv_Inh_FieldDecls :: MERelationEnv,meSortNameRoots_Inh_FieldDecls :: MESortNameRoots,meSortTypeName_Inh_FieldDecls :: MESortTypeName}
data Syn_FieldDecls = Syn_FieldDecls {desugared_Syn_FieldDecls :: (TcM [Core.FieldDecl]),namespaceDependencies_Syn_FieldDecls :: (TcM [Core.NamespaceTypeName]),self_Syn_FieldDecls :: FieldDecls,sortDependencies_Syn_FieldDecls :: (TcM [Core.SortTypeName])}
wrap_FieldDecls :: T_FieldDecls ->
                   Inh_FieldDecls ->
                   Syn_FieldDecls
wrap_FieldDecls sem (Inh_FieldDecls _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName) =
    (let ( _lhsOdesugared,_lhsOnamespaceDependencies,_lhsOself,_lhsOsortDependencies) = sem _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName
     in  (Syn_FieldDecls _lhsOdesugared _lhsOnamespaceDependencies _lhsOself _lhsOsortDependencies))
sem_FieldDecls_Cons :: T_FieldDecl ->
                       T_FieldDecls ->
                       T_FieldDecls
sem_FieldDecls_Cons hd_ tl_ =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOdesugared :: (TcM [Core.FieldDecl])
              _lhsOnamespaceDependencies :: (TcM [Core.NamespaceTypeName])
              _lhsOsortDependencies :: (TcM [Core.SortTypeName])
              _lhsOself :: FieldDecls
              _hdOmeEnvNameRoots :: MEEnvNameRoots
              _hdOmeEnvTypeName :: MEEnvTypeName
              _hdOmeFunType :: MEFunType
              _hdOmeNamespaceCtor :: MENamespaceCtor
              _hdOmeNamespaceNameRoots :: MENamespaceNameRoots
              _hdOmeNamespaceTypeName :: MENamespaceTypeName
              _hdOmeRelationEnv :: MERelationEnv
              _hdOmeSortNameRoots :: MESortNameRoots
              _hdOmeSortTypeName :: MESortTypeName
              _tlOmeEnvNameRoots :: MEEnvNameRoots
              _tlOmeEnvTypeName :: MEEnvTypeName
              _tlOmeFunType :: MEFunType
              _tlOmeNamespaceCtor :: MENamespaceCtor
              _tlOmeNamespaceNameRoots :: MENamespaceNameRoots
              _tlOmeNamespaceTypeName :: MENamespaceTypeName
              _tlOmeRelationEnv :: MERelationEnv
              _tlOmeSortNameRoots :: MESortNameRoots
              _tlOmeSortTypeName :: MESortTypeName
              _hdIdesugared :: (TcM Core.FieldDecl)
              _hdInamespaceDependencies :: (TcM [Core.NamespaceTypeName])
              _hdIself :: FieldDecl
              _hdIsortDependencies :: (TcM [Core.SortTypeName])
              _tlIdesugared :: (TcM [Core.FieldDecl])
              _tlInamespaceDependencies :: (TcM [Core.NamespaceTypeName])
              _tlIself :: FieldDecls
              _tlIsortDependencies :: (TcM [Core.SortTypeName])
              _lhsOdesugared =
                  ({-# LINE 174 "src/KnotSpec/Desugaring.ag" #-}
                   (consA _hdIdesugared _tlIdesugared)
                   {-# LINE 2150 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOnamespaceDependencies =
                  ({-# LINE 483 "src/KnotSpec/Desugaring.ag" #-}
                   (mappendA _hdInamespaceDependencies _tlInamespaceDependencies)
                   {-# LINE 2155 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOsortDependencies =
                  ({-# LINE 480 "src/KnotSpec/Desugaring.ag" #-}
                   (mappendA _hdIsortDependencies _tlIsortDependencies)
                   {-# LINE 2160 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _hdOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 2169 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 2174 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 2179 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 2184 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 2189 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 2194 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 2199 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 2204 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 2209 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 2214 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 2219 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 2224 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 2229 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 2234 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 2239 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 2244 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 2249 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 2254 "src/KnotSpec/AG.hs" #-}
                   )
              ( _hdIdesugared,_hdInamespaceDependencies,_hdIself,_hdIsortDependencies) =
                  hd_ _hdOmeEnvNameRoots _hdOmeEnvTypeName _hdOmeFunType _hdOmeNamespaceCtor _hdOmeNamespaceNameRoots _hdOmeNamespaceTypeName _hdOmeRelationEnv _hdOmeSortNameRoots _hdOmeSortTypeName
              ( _tlIdesugared,_tlInamespaceDependencies,_tlIself,_tlIsortDependencies) =
                  tl_ _tlOmeEnvNameRoots _tlOmeEnvTypeName _tlOmeFunType _tlOmeNamespaceCtor _tlOmeNamespaceNameRoots _tlOmeNamespaceTypeName _tlOmeRelationEnv _tlOmeSortNameRoots _tlOmeSortTypeName
          in  ( _lhsOdesugared,_lhsOnamespaceDependencies,_lhsOself,_lhsOsortDependencies)))
sem_FieldDecls_Nil :: T_FieldDecls
sem_FieldDecls_Nil =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOdesugared :: (TcM [Core.FieldDecl])
              _lhsOnamespaceDependencies :: (TcM [Core.NamespaceTypeName])
              _lhsOsortDependencies :: (TcM [Core.SortTypeName])
              _lhsOself :: FieldDecls
              _lhsOdesugared =
                  ({-# LINE 174 "src/KnotSpec/Desugaring.ag" #-}
                   memptyA
                   {-# LINE 2279 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOnamespaceDependencies =
                  ({-# LINE 483 "src/KnotSpec/Desugaring.ag" #-}
                   memptyA
                   {-# LINE 2284 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOsortDependencies =
                  ({-# LINE 480 "src/KnotSpec/Desugaring.ag" #-}
                   memptyA
                   {-# LINE 2289 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  []
              _lhsOself =
                  _self
          in  ( _lhsOdesugared,_lhsOnamespaceDependencies,_lhsOself,_lhsOsortDependencies)))
-- Formula -----------------------------------------------------
-- cata
sem_Formula :: Formula ->
               T_Formula
sem_Formula (FormBinding _fmlBinding) =
    (sem_Formula_FormBinding (sem_RuleBinding _fmlBinding))
sem_Formula (FormJudgement _fmlBindings _fmlJudgement) =
    (sem_Formula_FormJudgement (sem_RuleBindings _fmlBindings) (sem_Judgement _fmlJudgement))
-- semantic domain
type T_Formula = MEEnvNameRoots ->
                 MEEnvTypeName ->
                 MEFunType ->
                 MENamespaceCtor ->
                 MENamespaceNameRoots ->
                 MENamespaceTypeName ->
                 MERelationEnv ->
                 MESortNameRoots ->
                 MESortTypeName ->
                 ( (TcM Core.Formula),Formula)
data Inh_Formula = Inh_Formula {meEnvNameRoots_Inh_Formula :: MEEnvNameRoots,meEnvTypeName_Inh_Formula :: MEEnvTypeName,meFunType_Inh_Formula :: MEFunType,meNamespaceCtor_Inh_Formula :: MENamespaceCtor,meNamespaceNameRoots_Inh_Formula :: MENamespaceNameRoots,meNamespaceTypeName_Inh_Formula :: MENamespaceTypeName,meRelationEnv_Inh_Formula :: MERelationEnv,meSortNameRoots_Inh_Formula :: MESortNameRoots,meSortTypeName_Inh_Formula :: MESortTypeName}
data Syn_Formula = Syn_Formula {desugared_Syn_Formula :: (TcM Core.Formula),self_Syn_Formula :: Formula}
wrap_Formula :: T_Formula ->
                Inh_Formula ->
                Syn_Formula
wrap_Formula sem (Inh_Formula _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName) =
    (let ( _lhsOdesugared,_lhsOself) = sem _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName
     in  (Syn_Formula _lhsOdesugared _lhsOself))
sem_Formula_FormBinding :: T_RuleBinding ->
                           T_Formula
sem_Formula_FormBinding fmlBinding_ =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOself :: Formula
              _lhsOdesugared :: (TcM Core.Formula)
              _fmlBindingOmeEnvNameRoots :: MEEnvNameRoots
              _fmlBindingOmeEnvTypeName :: MEEnvTypeName
              _fmlBindingOmeFunType :: MEFunType
              _fmlBindingOmeNamespaceCtor :: MENamespaceCtor
              _fmlBindingOmeNamespaceNameRoots :: MENamespaceNameRoots
              _fmlBindingOmeNamespaceTypeName :: MENamespaceTypeName
              _fmlBindingOmeRelationEnv :: MERelationEnv
              _fmlBindingOmeSortNameRoots :: MESortNameRoots
              _fmlBindingOmeSortTypeName :: MESortTypeName
              _fmlBindingIdesugared :: (TcM Core.RuleBinding)
              _fmlBindingIself :: RuleBinding
              _desugared =
                  ({-# LINE 399 "src/KnotSpec/Desugaring.ag" #-}
                   Core.FormBinding <$> _fmlBindingIdesugared
                   {-# LINE 2351 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  FormBinding _fmlBindingIself
              _lhsOself =
                  _self
              _lhsOdesugared =
                  ({-# LINE 395 "src/KnotSpec/Desugaring.ag" #-}
                   _desugared
                   {-# LINE 2360 "src/KnotSpec/AG.hs" #-}
                   )
              _fmlBindingOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 2365 "src/KnotSpec/AG.hs" #-}
                   )
              _fmlBindingOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 2370 "src/KnotSpec/AG.hs" #-}
                   )
              _fmlBindingOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 2375 "src/KnotSpec/AG.hs" #-}
                   )
              _fmlBindingOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 2380 "src/KnotSpec/AG.hs" #-}
                   )
              _fmlBindingOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 2385 "src/KnotSpec/AG.hs" #-}
                   )
              _fmlBindingOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 2390 "src/KnotSpec/AG.hs" #-}
                   )
              _fmlBindingOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 2395 "src/KnotSpec/AG.hs" #-}
                   )
              _fmlBindingOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 2400 "src/KnotSpec/AG.hs" #-}
                   )
              _fmlBindingOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 2405 "src/KnotSpec/AG.hs" #-}
                   )
              ( _fmlBindingIdesugared,_fmlBindingIself) =
                  fmlBinding_ _fmlBindingOmeEnvNameRoots _fmlBindingOmeEnvTypeName _fmlBindingOmeFunType _fmlBindingOmeNamespaceCtor _fmlBindingOmeNamespaceNameRoots _fmlBindingOmeNamespaceTypeName _fmlBindingOmeRelationEnv _fmlBindingOmeSortNameRoots _fmlBindingOmeSortTypeName
          in  ( _lhsOdesugared,_lhsOself)))
sem_Formula_FormJudgement :: T_RuleBindings ->
                             T_Judgement ->
                             T_Formula
sem_Formula_FormJudgement fmlBindings_ fmlJudgement_ =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOself :: Formula
              _lhsOdesugared :: (TcM Core.Formula)
              _fmlBindingsOmeEnvNameRoots :: MEEnvNameRoots
              _fmlBindingsOmeEnvTypeName :: MEEnvTypeName
              _fmlBindingsOmeFunType :: MEFunType
              _fmlBindingsOmeNamespaceCtor :: MENamespaceCtor
              _fmlBindingsOmeNamespaceNameRoots :: MENamespaceNameRoots
              _fmlBindingsOmeNamespaceTypeName :: MENamespaceTypeName
              _fmlBindingsOmeRelationEnv :: MERelationEnv
              _fmlBindingsOmeSortNameRoots :: MESortNameRoots
              _fmlBindingsOmeSortTypeName :: MESortTypeName
              _fmlJudgementOmeEnvNameRoots :: MEEnvNameRoots
              _fmlJudgementOmeEnvTypeName :: MEEnvTypeName
              _fmlJudgementOmeFunType :: MEFunType
              _fmlJudgementOmeNamespaceCtor :: MENamespaceCtor
              _fmlJudgementOmeNamespaceNameRoots :: MENamespaceNameRoots
              _fmlJudgementOmeNamespaceTypeName :: MENamespaceTypeName
              _fmlJudgementOmeRelationEnv :: MERelationEnv
              _fmlJudgementOmeSortNameRoots :: MESortNameRoots
              _fmlJudgementOmeSortTypeName :: MESortTypeName
              _fmlBindingsIdesugared :: (TcM [Core.RuleBinding])
              _fmlBindingsIself :: RuleBindings
              _fmlJudgementIdesugared :: (TcM Core.Judgement)
              _fmlJudgementIself :: Judgement
              _desugared =
                  ({-# LINE 401 "src/KnotSpec/Desugaring.ag" #-}
                   do
                     rbs <- _fmlBindingsIdesugared
                     Core.Judgement rtn mbEnv sts <- _fmlJudgementIdesugared
                     return $
                       Core.FormJudgement rbs rtn mbEnv sts
                   {-# LINE 2454 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  FormJudgement _fmlBindingsIself _fmlJudgementIself
              _lhsOself =
                  _self
              _lhsOdesugared =
                  ({-# LINE 395 "src/KnotSpec/Desugaring.ag" #-}
                   _desugared
                   {-# LINE 2463 "src/KnotSpec/AG.hs" #-}
                   )
              _fmlBindingsOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 2468 "src/KnotSpec/AG.hs" #-}
                   )
              _fmlBindingsOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 2473 "src/KnotSpec/AG.hs" #-}
                   )
              _fmlBindingsOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 2478 "src/KnotSpec/AG.hs" #-}
                   )
              _fmlBindingsOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 2483 "src/KnotSpec/AG.hs" #-}
                   )
              _fmlBindingsOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 2488 "src/KnotSpec/AG.hs" #-}
                   )
              _fmlBindingsOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 2493 "src/KnotSpec/AG.hs" #-}
                   )
              _fmlBindingsOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 2498 "src/KnotSpec/AG.hs" #-}
                   )
              _fmlBindingsOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 2503 "src/KnotSpec/AG.hs" #-}
                   )
              _fmlBindingsOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 2508 "src/KnotSpec/AG.hs" #-}
                   )
              _fmlJudgementOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 2513 "src/KnotSpec/AG.hs" #-}
                   )
              _fmlJudgementOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 2518 "src/KnotSpec/AG.hs" #-}
                   )
              _fmlJudgementOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 2523 "src/KnotSpec/AG.hs" #-}
                   )
              _fmlJudgementOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 2528 "src/KnotSpec/AG.hs" #-}
                   )
              _fmlJudgementOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 2533 "src/KnotSpec/AG.hs" #-}
                   )
              _fmlJudgementOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 2538 "src/KnotSpec/AG.hs" #-}
                   )
              _fmlJudgementOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 2543 "src/KnotSpec/AG.hs" #-}
                   )
              _fmlJudgementOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 2548 "src/KnotSpec/AG.hs" #-}
                   )
              _fmlJudgementOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 2553 "src/KnotSpec/AG.hs" #-}
                   )
              ( _fmlBindingsIdesugared,_fmlBindingsIself) =
                  fmlBindings_ _fmlBindingsOmeEnvNameRoots _fmlBindingsOmeEnvTypeName _fmlBindingsOmeFunType _fmlBindingsOmeNamespaceCtor _fmlBindingsOmeNamespaceNameRoots _fmlBindingsOmeNamespaceTypeName _fmlBindingsOmeRelationEnv _fmlBindingsOmeSortNameRoots _fmlBindingsOmeSortTypeName
              ( _fmlJudgementIdesugared,_fmlJudgementIself) =
                  fmlJudgement_ _fmlJudgementOmeEnvNameRoots _fmlJudgementOmeEnvTypeName _fmlJudgementOmeFunType _fmlJudgementOmeNamespaceCtor _fmlJudgementOmeNamespaceNameRoots _fmlJudgementOmeNamespaceTypeName _fmlJudgementOmeRelationEnv _fmlJudgementOmeSortNameRoots _fmlJudgementOmeSortTypeName
          in  ( _lhsOdesugared,_lhsOself)))
-- Formulas ----------------------------------------------------
-- cata
sem_Formulas :: Formulas ->
                T_Formulas
sem_Formulas list =
    (Prelude.foldr sem_Formulas_Cons sem_Formulas_Nil (Prelude.map sem_Formula list))
-- semantic domain
type T_Formulas = MEEnvNameRoots ->
                  MEEnvTypeName ->
                  MEFunType ->
                  MENamespaceCtor ->
                  MENamespaceNameRoots ->
                  MENamespaceTypeName ->
                  MERelationEnv ->
                  MESortNameRoots ->
                  MESortTypeName ->
                  ( (TcM [Core.Formula]),Formulas)
data Inh_Formulas = Inh_Formulas {meEnvNameRoots_Inh_Formulas :: MEEnvNameRoots,meEnvTypeName_Inh_Formulas :: MEEnvTypeName,meFunType_Inh_Formulas :: MEFunType,meNamespaceCtor_Inh_Formulas :: MENamespaceCtor,meNamespaceNameRoots_Inh_Formulas :: MENamespaceNameRoots,meNamespaceTypeName_Inh_Formulas :: MENamespaceTypeName,meRelationEnv_Inh_Formulas :: MERelationEnv,meSortNameRoots_Inh_Formulas :: MESortNameRoots,meSortTypeName_Inh_Formulas :: MESortTypeName}
data Syn_Formulas = Syn_Formulas {desugared_Syn_Formulas :: (TcM [Core.Formula]),self_Syn_Formulas :: Formulas}
wrap_Formulas :: T_Formulas ->
                 Inh_Formulas ->
                 Syn_Formulas
wrap_Formulas sem (Inh_Formulas _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName) =
    (let ( _lhsOdesugared,_lhsOself) = sem _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName
     in  (Syn_Formulas _lhsOdesugared _lhsOself))
sem_Formulas_Cons :: T_Formula ->
                     T_Formulas ->
                     T_Formulas
sem_Formulas_Cons hd_ tl_ =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOdesugared :: (TcM [Core.Formula])
              _lhsOself :: Formulas
              _hdOmeEnvNameRoots :: MEEnvNameRoots
              _hdOmeEnvTypeName :: MEEnvTypeName
              _hdOmeFunType :: MEFunType
              _hdOmeNamespaceCtor :: MENamespaceCtor
              _hdOmeNamespaceNameRoots :: MENamespaceNameRoots
              _hdOmeNamespaceTypeName :: MENamespaceTypeName
              _hdOmeRelationEnv :: MERelationEnv
              _hdOmeSortNameRoots :: MESortNameRoots
              _hdOmeSortTypeName :: MESortTypeName
              _tlOmeEnvNameRoots :: MEEnvNameRoots
              _tlOmeEnvTypeName :: MEEnvTypeName
              _tlOmeFunType :: MEFunType
              _tlOmeNamespaceCtor :: MENamespaceCtor
              _tlOmeNamespaceNameRoots :: MENamespaceNameRoots
              _tlOmeNamespaceTypeName :: MENamespaceTypeName
              _tlOmeRelationEnv :: MERelationEnv
              _tlOmeSortNameRoots :: MESortNameRoots
              _tlOmeSortTypeName :: MESortTypeName
              _hdIdesugared :: (TcM Core.Formula)
              _hdIself :: Formula
              _tlIdesugared :: (TcM [Core.Formula])
              _tlIself :: Formulas
              _lhsOdesugared =
                  ({-# LINE 394 "src/KnotSpec/Desugaring.ag" #-}
                   (consA _hdIdesugared _tlIdesugared)
                   {-# LINE 2625 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _hdOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 2634 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 2639 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 2644 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 2649 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 2654 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 2659 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 2664 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 2669 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 2674 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 2679 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 2684 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 2689 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 2694 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 2699 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 2704 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 2709 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 2714 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 2719 "src/KnotSpec/AG.hs" #-}
                   )
              ( _hdIdesugared,_hdIself) =
                  hd_ _hdOmeEnvNameRoots _hdOmeEnvTypeName _hdOmeFunType _hdOmeNamespaceCtor _hdOmeNamespaceNameRoots _hdOmeNamespaceTypeName _hdOmeRelationEnv _hdOmeSortNameRoots _hdOmeSortTypeName
              ( _tlIdesugared,_tlIself) =
                  tl_ _tlOmeEnvNameRoots _tlOmeEnvTypeName _tlOmeFunType _tlOmeNamespaceCtor _tlOmeNamespaceNameRoots _tlOmeNamespaceTypeName _tlOmeRelationEnv _tlOmeSortNameRoots _tlOmeSortTypeName
          in  ( _lhsOdesugared,_lhsOself)))
sem_Formulas_Nil :: T_Formulas
sem_Formulas_Nil =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOdesugared :: (TcM [Core.Formula])
              _lhsOself :: Formulas
              _lhsOdesugared =
                  ({-# LINE 394 "src/KnotSpec/Desugaring.ag" #-}
                   memptyA
                   {-# LINE 2742 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  []
              _lhsOself =
                  _self
          in  ( _lhsOdesugared,_lhsOself)))
-- FunCase -----------------------------------------------------
-- cata
sem_FunCase :: FunCase ->
               T_FunCase
sem_FunCase (FunCase _fcCtor _fcFields _fcRhs) =
    (sem_FunCase_FunCase _fcCtor (sem_Names _fcFields) (sem_Vle _fcRhs))
-- semantic domain
type T_FunCase = MEEnvNameRoots ->
                 MEEnvTypeName ->
                 MEFunType ->
                 MENamespaceCtor ->
                 MENamespaceNameRoots ->
                 MENamespaceTypeName ->
                 MERelationEnv ->
                 MESortNameRoots ->
                 MESortTypeName ->
                 ( (TcM Core.FunCase),FunCase)
data Inh_FunCase = Inh_FunCase {meEnvNameRoots_Inh_FunCase :: MEEnvNameRoots,meEnvTypeName_Inh_FunCase :: MEEnvTypeName,meFunType_Inh_FunCase :: MEFunType,meNamespaceCtor_Inh_FunCase :: MENamespaceCtor,meNamespaceNameRoots_Inh_FunCase :: MENamespaceNameRoots,meNamespaceTypeName_Inh_FunCase :: MENamespaceTypeName,meRelationEnv_Inh_FunCase :: MERelationEnv,meSortNameRoots_Inh_FunCase :: MESortNameRoots,meSortTypeName_Inh_FunCase :: MESortTypeName}
data Syn_FunCase = Syn_FunCase {desugared_Syn_FunCase :: (TcM Core.FunCase),self_Syn_FunCase :: FunCase}
wrap_FunCase :: T_FunCase ->
                Inh_FunCase ->
                Syn_FunCase
wrap_FunCase sem (Inh_FunCase _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName) =
    (let ( _lhsOdesugared,_lhsOself) = sem _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName
     in  (Syn_FunCase _lhsOdesugared _lhsOself))
sem_FunCase_FunCase :: CtorName ->
                       T_Names ->
                       T_Vle ->
                       T_FunCase
sem_FunCase_FunCase fcCtor_ fcFields_ fcRhs_ =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOself :: FunCase
              _lhsOdesugared :: (TcM Core.FunCase)
              _fcFieldsOmeEnvNameRoots :: MEEnvNameRoots
              _fcFieldsOmeEnvTypeName :: MEEnvTypeName
              _fcFieldsOmeFunType :: MEFunType
              _fcFieldsOmeNamespaceCtor :: MENamespaceCtor
              _fcFieldsOmeNamespaceNameRoots :: MENamespaceNameRoots
              _fcFieldsOmeNamespaceTypeName :: MENamespaceTypeName
              _fcFieldsOmeRelationEnv :: MERelationEnv
              _fcFieldsOmeSortNameRoots :: MESortNameRoots
              _fcFieldsOmeSortTypeName :: MESortTypeName
              _fcRhsOmeEnvNameRoots :: MEEnvNameRoots
              _fcRhsOmeEnvTypeName :: MEEnvTypeName
              _fcRhsOmeFunType :: MEFunType
              _fcRhsOmeNamespaceCtor :: MENamespaceCtor
              _fcRhsOmeNamespaceNameRoots :: MENamespaceNameRoots
              _fcRhsOmeNamespaceTypeName :: MENamespaceTypeName
              _fcRhsOmeRelationEnv :: MERelationEnv
              _fcRhsOmeSortNameRoots :: MESortNameRoots
              _fcRhsOmeSortTypeName :: MESortTypeName
              _fcFieldsIfieldMetaBinding :: (TcM [Core.FieldMetaBinding])
              _fcFieldsIself :: Names
              _fcFieldsIsubtreeName :: (TcM [Core.SubtreeVar])
              _fcRhsIdesugared :: (TcM Core.Vle)
              _fcRhsIself :: Vle
              _desugared =
                  ({-# LINE 289 "src/KnotSpec/Desugaring.ag" #-}
                   Core.FunCase (Core.CNO fcCtor_)
                     <$> _fcFieldsIfieldMetaBinding
                     <*> _fcRhsIdesugared
                   {-# LINE 2818 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  FunCase fcCtor_ _fcFieldsIself _fcRhsIself
              _lhsOself =
                  _self
              _lhsOdesugared =
                  ({-# LINE 179 "src/KnotSpec/Desugaring.ag" #-}
                   _desugared
                   {-# LINE 2827 "src/KnotSpec/AG.hs" #-}
                   )
              _fcFieldsOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 2832 "src/KnotSpec/AG.hs" #-}
                   )
              _fcFieldsOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 2837 "src/KnotSpec/AG.hs" #-}
                   )
              _fcFieldsOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 2842 "src/KnotSpec/AG.hs" #-}
                   )
              _fcFieldsOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 2847 "src/KnotSpec/AG.hs" #-}
                   )
              _fcFieldsOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 2852 "src/KnotSpec/AG.hs" #-}
                   )
              _fcFieldsOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 2857 "src/KnotSpec/AG.hs" #-}
                   )
              _fcFieldsOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 2862 "src/KnotSpec/AG.hs" #-}
                   )
              _fcFieldsOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 2867 "src/KnotSpec/AG.hs" #-}
                   )
              _fcFieldsOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 2872 "src/KnotSpec/AG.hs" #-}
                   )
              _fcRhsOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 2877 "src/KnotSpec/AG.hs" #-}
                   )
              _fcRhsOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 2882 "src/KnotSpec/AG.hs" #-}
                   )
              _fcRhsOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 2887 "src/KnotSpec/AG.hs" #-}
                   )
              _fcRhsOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 2892 "src/KnotSpec/AG.hs" #-}
                   )
              _fcRhsOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 2897 "src/KnotSpec/AG.hs" #-}
                   )
              _fcRhsOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 2902 "src/KnotSpec/AG.hs" #-}
                   )
              _fcRhsOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 2907 "src/KnotSpec/AG.hs" #-}
                   )
              _fcRhsOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 2912 "src/KnotSpec/AG.hs" #-}
                   )
              _fcRhsOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 2917 "src/KnotSpec/AG.hs" #-}
                   )
              ( _fcFieldsIfieldMetaBinding,_fcFieldsIself,_fcFieldsIsubtreeName) =
                  fcFields_ _fcFieldsOmeEnvNameRoots _fcFieldsOmeEnvTypeName _fcFieldsOmeFunType _fcFieldsOmeNamespaceCtor _fcFieldsOmeNamespaceNameRoots _fcFieldsOmeNamespaceTypeName _fcFieldsOmeRelationEnv _fcFieldsOmeSortNameRoots _fcFieldsOmeSortTypeName
              ( _fcRhsIdesugared,_fcRhsIself) =
                  fcRhs_ _fcRhsOmeEnvNameRoots _fcRhsOmeEnvTypeName _fcRhsOmeFunType _fcRhsOmeNamespaceCtor _fcRhsOmeNamespaceNameRoots _fcRhsOmeNamespaceTypeName _fcRhsOmeRelationEnv _fcRhsOmeSortNameRoots _fcRhsOmeSortTypeName
          in  ( _lhsOdesugared,_lhsOself)))
-- FunCases ----------------------------------------------------
-- cata
sem_FunCases :: FunCases ->
                T_FunCases
sem_FunCases list =
    (Prelude.foldr sem_FunCases_Cons sem_FunCases_Nil (Prelude.map sem_FunCase list))
-- semantic domain
type T_FunCases = MEEnvNameRoots ->
                  MEEnvTypeName ->
                  MEFunType ->
                  MENamespaceCtor ->
                  MENamespaceNameRoots ->
                  MENamespaceTypeName ->
                  MERelationEnv ->
                  MESortNameRoots ->
                  MESortTypeName ->
                  ( (TcM [Core.FunCase]),FunCases)
data Inh_FunCases = Inh_FunCases {meEnvNameRoots_Inh_FunCases :: MEEnvNameRoots,meEnvTypeName_Inh_FunCases :: MEEnvTypeName,meFunType_Inh_FunCases :: MEFunType,meNamespaceCtor_Inh_FunCases :: MENamespaceCtor,meNamespaceNameRoots_Inh_FunCases :: MENamespaceNameRoots,meNamespaceTypeName_Inh_FunCases :: MENamespaceTypeName,meRelationEnv_Inh_FunCases :: MERelationEnv,meSortNameRoots_Inh_FunCases :: MESortNameRoots,meSortTypeName_Inh_FunCases :: MESortTypeName}
data Syn_FunCases = Syn_FunCases {desugared_Syn_FunCases :: (TcM [Core.FunCase]),self_Syn_FunCases :: FunCases}
wrap_FunCases :: T_FunCases ->
                 Inh_FunCases ->
                 Syn_FunCases
wrap_FunCases sem (Inh_FunCases _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName) =
    (let ( _lhsOdesugared,_lhsOself) = sem _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName
     in  (Syn_FunCases _lhsOdesugared _lhsOself))
sem_FunCases_Cons :: T_FunCase ->
                     T_FunCases ->
                     T_FunCases
sem_FunCases_Cons hd_ tl_ =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOdesugared :: (TcM [Core.FunCase])
              _lhsOself :: FunCases
              _hdOmeEnvNameRoots :: MEEnvNameRoots
              _hdOmeEnvTypeName :: MEEnvTypeName
              _hdOmeFunType :: MEFunType
              _hdOmeNamespaceCtor :: MENamespaceCtor
              _hdOmeNamespaceNameRoots :: MENamespaceNameRoots
              _hdOmeNamespaceTypeName :: MENamespaceTypeName
              _hdOmeRelationEnv :: MERelationEnv
              _hdOmeSortNameRoots :: MESortNameRoots
              _hdOmeSortTypeName :: MESortTypeName
              _tlOmeEnvNameRoots :: MEEnvNameRoots
              _tlOmeEnvTypeName :: MEEnvTypeName
              _tlOmeFunType :: MEFunType
              _tlOmeNamespaceCtor :: MENamespaceCtor
              _tlOmeNamespaceNameRoots :: MENamespaceNameRoots
              _tlOmeNamespaceTypeName :: MENamespaceTypeName
              _tlOmeRelationEnv :: MERelationEnv
              _tlOmeSortNameRoots :: MESortNameRoots
              _tlOmeSortTypeName :: MESortTypeName
              _hdIdesugared :: (TcM Core.FunCase)
              _hdIself :: FunCase
              _tlIdesugared :: (TcM [Core.FunCase])
              _tlIself :: FunCases
              _lhsOdesugared =
                  ({-# LINE 178 "src/KnotSpec/Desugaring.ag" #-}
                   (consA _hdIdesugared _tlIdesugared)
                   {-# LINE 2989 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _hdOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 2998 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 3003 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 3008 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 3013 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 3018 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 3023 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 3028 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 3033 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 3038 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 3043 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 3048 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 3053 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 3058 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 3063 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 3068 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 3073 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 3078 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 3083 "src/KnotSpec/AG.hs" #-}
                   )
              ( _hdIdesugared,_hdIself) =
                  hd_ _hdOmeEnvNameRoots _hdOmeEnvTypeName _hdOmeFunType _hdOmeNamespaceCtor _hdOmeNamespaceNameRoots _hdOmeNamespaceTypeName _hdOmeRelationEnv _hdOmeSortNameRoots _hdOmeSortTypeName
              ( _tlIdesugared,_tlIself) =
                  tl_ _tlOmeEnvNameRoots _tlOmeEnvTypeName _tlOmeFunType _tlOmeNamespaceCtor _tlOmeNamespaceNameRoots _tlOmeNamespaceTypeName _tlOmeRelationEnv _tlOmeSortNameRoots _tlOmeSortTypeName
          in  ( _lhsOdesugared,_lhsOself)))
sem_FunCases_Nil :: T_FunCases
sem_FunCases_Nil =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOdesugared :: (TcM [Core.FunCase])
              _lhsOself :: FunCases
              _lhsOdesugared =
                  ({-# LINE 178 "src/KnotSpec/Desugaring.ag" #-}
                   memptyA
                   {-# LINE 3106 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  []
              _lhsOself =
                  _self
          in  ( _lhsOdesugared,_lhsOself)))
-- FunDecl -----------------------------------------------------
-- cata
sem_FunDecl :: FunDecl ->
               T_FunDecl
sem_FunDecl (FunDecl _fdName _fdSource _fdTarget _fdCases) =
    (sem_FunDecl_FunDecl _fdName (sem_TypeName _fdSource) (sem_TypeNames _fdTarget) (sem_FunCases _fdCases))
-- semantic domain
type T_FunDecl = MEEnvNameRoots ->
                 MEEnvTypeName ->
                 MEFunType ->
                 MENamespaceCtor ->
                 MENamespaceNameRoots ->
                 MENamespaceTypeName ->
                 MERelationEnv ->
                 MESortNameRoots ->
                 MESortTypeName ->
                 ( (TcM Core.FunDecl),(TcM Core.FunctionEnv),FunDecl,MEFunType)
data Inh_FunDecl = Inh_FunDecl {meEnvNameRoots_Inh_FunDecl :: MEEnvNameRoots,meEnvTypeName_Inh_FunDecl :: MEEnvTypeName,meFunType_Inh_FunDecl :: MEFunType,meNamespaceCtor_Inh_FunDecl :: MENamespaceCtor,meNamespaceNameRoots_Inh_FunDecl :: MENamespaceNameRoots,meNamespaceTypeName_Inh_FunDecl :: MENamespaceTypeName,meRelationEnv_Inh_FunDecl :: MERelationEnv,meSortNameRoots_Inh_FunDecl :: MESortNameRoots,meSortTypeName_Inh_FunDecl :: MESortTypeName}
data Syn_FunDecl = Syn_FunDecl {desugared_Syn_FunDecl :: (TcM Core.FunDecl),sFunctionDef_Syn_FunDecl :: (TcM Core.FunctionEnv),self_Syn_FunDecl :: FunDecl,smeFunType_Syn_FunDecl :: MEFunType}
wrap_FunDecl :: T_FunDecl ->
                Inh_FunDecl ->
                Syn_FunDecl
wrap_FunDecl sem (Inh_FunDecl _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName) =
    (let ( _lhsOdesugared,_lhsOsFunctionDef,_lhsOself,_lhsOsmeFunType) = sem _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName
     in  (Syn_FunDecl _lhsOdesugared _lhsOsFunctionDef _lhsOself _lhsOsmeFunType))
sem_FunDecl_FunDecl :: FunName ->
                       T_TypeName ->
                       T_TypeNames ->
                       T_FunCases ->
                       T_FunDecl
sem_FunDecl_FunDecl fdName_ fdSource_ fdTarget_ fdCases_ =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOsFunctionDef :: (TcM Core.FunctionEnv)
              _lhsOsmeFunType :: MEFunType
              _lhsOself :: FunDecl
              _lhsOdesugared :: (TcM Core.FunDecl)
              _fdSourceOmeEnvNameRoots :: MEEnvNameRoots
              _fdSourceOmeEnvTypeName :: MEEnvTypeName
              _fdSourceOmeFunType :: MEFunType
              _fdSourceOmeNamespaceCtor :: MENamespaceCtor
              _fdSourceOmeNamespaceNameRoots :: MENamespaceNameRoots
              _fdSourceOmeNamespaceTypeName :: MENamespaceTypeName
              _fdSourceOmeRelationEnv :: MERelationEnv
              _fdSourceOmeSortNameRoots :: MESortNameRoots
              _fdSourceOmeSortTypeName :: MESortTypeName
              _fdTargetOmeEnvNameRoots :: MEEnvNameRoots
              _fdTargetOmeEnvTypeName :: MEEnvTypeName
              _fdTargetOmeFunType :: MEFunType
              _fdTargetOmeNamespaceCtor :: MENamespaceCtor
              _fdTargetOmeNamespaceNameRoots :: MENamespaceNameRoots
              _fdTargetOmeNamespaceTypeName :: MENamespaceTypeName
              _fdTargetOmeRelationEnv :: MERelationEnv
              _fdTargetOmeSortNameRoots :: MESortNameRoots
              _fdTargetOmeSortTypeName :: MESortTypeName
              _fdCasesOmeEnvNameRoots :: MEEnvNameRoots
              _fdCasesOmeEnvTypeName :: MEEnvTypeName
              _fdCasesOmeFunType :: MEFunType
              _fdCasesOmeNamespaceCtor :: MENamespaceCtor
              _fdCasesOmeNamespaceNameRoots :: MENamespaceNameRoots
              _fdCasesOmeNamespaceTypeName :: MENamespaceTypeName
              _fdCasesOmeRelationEnv :: MERelationEnv
              _fdCasesOmeSortNameRoots :: MESortNameRoots
              _fdCasesOmeSortTypeName :: MESortTypeName
              _fdSourceIfromTn :: String
              _fdSourceInamespaceTypeName :: (TcM Core.NamespaceTypeName)
              _fdSourceIrelationTypeName :: (TcM Core.RelationTypeName)
              _fdSourceIself :: TypeName
              _fdSourceIsortTypeName :: (TcM Core.SortTypeName)
              _fdTargetInamespaceTypeName :: (TcM [Core.NamespaceTypeName])
              _fdTargetIself :: TypeNames
              _fdCasesIdesugared :: (TcM [Core.FunCase])
              _fdCasesIself :: FunCases
              _desugared =
                  ({-# LINE 276 "src/KnotSpec/Desugaring.ag" #-}
                   do
                     stn  <- _fdSourceIsortTypeName
                     ntns <- _fdTargetInamespaceTypeName
                     nr <- case Data.Map.lookup _fdSourceIself _lhsImeSortNameRoots of
                             Just nrs -> return (head nrs)
                             Nothing  -> throwError "No nameroots for function domain"
                     let matchItem = Core.SubtreeVar (Core.NR $ fromNR nr) "" stn
                     Core.FunDecl (Core.FN fdName_ stn ntns) stn ntns matchItem
                       <$> _fdCasesIdesugared
                   {-# LINE 3204 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOsFunctionDef =
                  ({-# LINE 607 "src/KnotSpec/Desugaring.ag" #-}
                   do
                     source <- _fdSourceIsortTypeName
                     target <- _fdTargetInamespaceTypeName
                     return $
                       Data.Map.singleton source
                         (Data.Map.singleton (Core.FN fdName_ source target) target)
                   {-# LINE 3214 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOsmeFunType =
                  ({-# LINE 182 "src/KnotSpec/Environment.ag" #-}
                   Data.Map.singleton fdName_ (_fdSourceIself,_fdTargetIself)
                   {-# LINE 3219 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  FunDecl fdName_ _fdSourceIself _fdTargetIself _fdCasesIself
              _lhsOself =
                  _self
              _lhsOdesugared =
                  ({-# LINE 177 "src/KnotSpec/Desugaring.ag" #-}
                   _desugared
                   {-# LINE 3228 "src/KnotSpec/AG.hs" #-}
                   )
              _fdSourceOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 3233 "src/KnotSpec/AG.hs" #-}
                   )
              _fdSourceOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 3238 "src/KnotSpec/AG.hs" #-}
                   )
              _fdSourceOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 3243 "src/KnotSpec/AG.hs" #-}
                   )
              _fdSourceOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 3248 "src/KnotSpec/AG.hs" #-}
                   )
              _fdSourceOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 3253 "src/KnotSpec/AG.hs" #-}
                   )
              _fdSourceOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 3258 "src/KnotSpec/AG.hs" #-}
                   )
              _fdSourceOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 3263 "src/KnotSpec/AG.hs" #-}
                   )
              _fdSourceOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 3268 "src/KnotSpec/AG.hs" #-}
                   )
              _fdSourceOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 3273 "src/KnotSpec/AG.hs" #-}
                   )
              _fdTargetOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 3278 "src/KnotSpec/AG.hs" #-}
                   )
              _fdTargetOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 3283 "src/KnotSpec/AG.hs" #-}
                   )
              _fdTargetOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 3288 "src/KnotSpec/AG.hs" #-}
                   )
              _fdTargetOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 3293 "src/KnotSpec/AG.hs" #-}
                   )
              _fdTargetOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 3298 "src/KnotSpec/AG.hs" #-}
                   )
              _fdTargetOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 3303 "src/KnotSpec/AG.hs" #-}
                   )
              _fdTargetOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 3308 "src/KnotSpec/AG.hs" #-}
                   )
              _fdTargetOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 3313 "src/KnotSpec/AG.hs" #-}
                   )
              _fdTargetOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 3318 "src/KnotSpec/AG.hs" #-}
                   )
              _fdCasesOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 3323 "src/KnotSpec/AG.hs" #-}
                   )
              _fdCasesOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 3328 "src/KnotSpec/AG.hs" #-}
                   )
              _fdCasesOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 3333 "src/KnotSpec/AG.hs" #-}
                   )
              _fdCasesOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 3338 "src/KnotSpec/AG.hs" #-}
                   )
              _fdCasesOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 3343 "src/KnotSpec/AG.hs" #-}
                   )
              _fdCasesOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 3348 "src/KnotSpec/AG.hs" #-}
                   )
              _fdCasesOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 3353 "src/KnotSpec/AG.hs" #-}
                   )
              _fdCasesOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 3358 "src/KnotSpec/AG.hs" #-}
                   )
              _fdCasesOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 3363 "src/KnotSpec/AG.hs" #-}
                   )
              ( _fdSourceIfromTn,_fdSourceInamespaceTypeName,_fdSourceIrelationTypeName,_fdSourceIself,_fdSourceIsortTypeName) =
                  fdSource_ _fdSourceOmeEnvNameRoots _fdSourceOmeEnvTypeName _fdSourceOmeFunType _fdSourceOmeNamespaceCtor _fdSourceOmeNamespaceNameRoots _fdSourceOmeNamespaceTypeName _fdSourceOmeRelationEnv _fdSourceOmeSortNameRoots _fdSourceOmeSortTypeName
              ( _fdTargetInamespaceTypeName,_fdTargetIself) =
                  fdTarget_ _fdTargetOmeEnvNameRoots _fdTargetOmeEnvTypeName _fdTargetOmeFunType _fdTargetOmeNamespaceCtor _fdTargetOmeNamespaceNameRoots _fdTargetOmeNamespaceTypeName _fdTargetOmeRelationEnv _fdTargetOmeSortNameRoots _fdTargetOmeSortTypeName
              ( _fdCasesIdesugared,_fdCasesIself) =
                  fdCases_ _fdCasesOmeEnvNameRoots _fdCasesOmeEnvTypeName _fdCasesOmeFunType _fdCasesOmeNamespaceCtor _fdCasesOmeNamespaceNameRoots _fdCasesOmeNamespaceTypeName _fdCasesOmeRelationEnv _fdCasesOmeSortNameRoots _fdCasesOmeSortTypeName
          in  ( _lhsOdesugared,_lhsOsFunctionDef,_lhsOself,_lhsOsmeFunType)))
-- FunDecls ----------------------------------------------------
-- cata
sem_FunDecls :: FunDecls ->
                T_FunDecls
sem_FunDecls list =
    (Prelude.foldr sem_FunDecls_Cons sem_FunDecls_Nil (Prelude.map sem_FunDecl list))
-- semantic domain
type T_FunDecls = MEEnvNameRoots ->
                  MEEnvTypeName ->
                  MEFunType ->
                  MENamespaceCtor ->
                  MENamespaceNameRoots ->
                  MENamespaceTypeName ->
                  MERelationEnv ->
                  MESortNameRoots ->
                  MESortTypeName ->
                  ( (TcM [Core.FunDecl]),(TcM Core.FunctionEnv),FunDecls,MEFunType)
data Inh_FunDecls = Inh_FunDecls {meEnvNameRoots_Inh_FunDecls :: MEEnvNameRoots,meEnvTypeName_Inh_FunDecls :: MEEnvTypeName,meFunType_Inh_FunDecls :: MEFunType,meNamespaceCtor_Inh_FunDecls :: MENamespaceCtor,meNamespaceNameRoots_Inh_FunDecls :: MENamespaceNameRoots,meNamespaceTypeName_Inh_FunDecls :: MENamespaceTypeName,meRelationEnv_Inh_FunDecls :: MERelationEnv,meSortNameRoots_Inh_FunDecls :: MESortNameRoots,meSortTypeName_Inh_FunDecls :: MESortTypeName}
data Syn_FunDecls = Syn_FunDecls {desugared_Syn_FunDecls :: (TcM [Core.FunDecl]),sFunctionDef_Syn_FunDecls :: (TcM Core.FunctionEnv),self_Syn_FunDecls :: FunDecls,smeFunType_Syn_FunDecls :: MEFunType}
wrap_FunDecls :: T_FunDecls ->
                 Inh_FunDecls ->
                 Syn_FunDecls
wrap_FunDecls sem (Inh_FunDecls _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName) =
    (let ( _lhsOdesugared,_lhsOsFunctionDef,_lhsOself,_lhsOsmeFunType) = sem _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName
     in  (Syn_FunDecls _lhsOdesugared _lhsOsFunctionDef _lhsOself _lhsOsmeFunType))
sem_FunDecls_Cons :: T_FunDecl ->
                     T_FunDecls ->
                     T_FunDecls
sem_FunDecls_Cons hd_ tl_ =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOdesugared :: (TcM [Core.FunDecl])
              _lhsOsFunctionDef :: (TcM Core.FunctionEnv)
              _lhsOsmeFunType :: MEFunType
              _lhsOself :: FunDecls
              _hdOmeEnvNameRoots :: MEEnvNameRoots
              _hdOmeEnvTypeName :: MEEnvTypeName
              _hdOmeFunType :: MEFunType
              _hdOmeNamespaceCtor :: MENamespaceCtor
              _hdOmeNamespaceNameRoots :: MENamespaceNameRoots
              _hdOmeNamespaceTypeName :: MENamespaceTypeName
              _hdOmeRelationEnv :: MERelationEnv
              _hdOmeSortNameRoots :: MESortNameRoots
              _hdOmeSortTypeName :: MESortTypeName
              _tlOmeEnvNameRoots :: MEEnvNameRoots
              _tlOmeEnvTypeName :: MEEnvTypeName
              _tlOmeFunType :: MEFunType
              _tlOmeNamespaceCtor :: MENamespaceCtor
              _tlOmeNamespaceNameRoots :: MENamespaceNameRoots
              _tlOmeNamespaceTypeName :: MENamespaceTypeName
              _tlOmeRelationEnv :: MERelationEnv
              _tlOmeSortNameRoots :: MESortNameRoots
              _tlOmeSortTypeName :: MESortTypeName
              _hdIdesugared :: (TcM Core.FunDecl)
              _hdIsFunctionDef :: (TcM Core.FunctionEnv)
              _hdIself :: FunDecl
              _hdIsmeFunType :: MEFunType
              _tlIdesugared :: (TcM [Core.FunDecl])
              _tlIsFunctionDef :: (TcM Core.FunctionEnv)
              _tlIself :: FunDecls
              _tlIsmeFunType :: MEFunType
              _lhsOdesugared =
                  ({-# LINE 176 "src/KnotSpec/Desugaring.ag" #-}
                   (consA _hdIdesugared _tlIdesugared)
                   {-# LINE 3443 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOsFunctionDef =
                  ({-# LINE 603 "src/KnotSpec/Desugaring.ag" #-}
                   (liftA2 (Data.Map.unionWith Data.Map.union) _hdIsFunctionDef _tlIsFunctionDef)
                   {-# LINE 3448 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOsmeFunType =
                  ({-# LINE 173 "src/KnotSpec/Environment.ag" #-}
                   (Data.Map.unionWith (error "smeFunType union") _hdIsmeFunType _tlIsmeFunType)
                   {-# LINE 3453 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _hdOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 3462 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 3467 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 3472 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 3477 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 3482 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 3487 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 3492 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 3497 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 3502 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 3507 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 3512 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 3517 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 3522 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 3527 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 3532 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 3537 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 3542 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 3547 "src/KnotSpec/AG.hs" #-}
                   )
              ( _hdIdesugared,_hdIsFunctionDef,_hdIself,_hdIsmeFunType) =
                  hd_ _hdOmeEnvNameRoots _hdOmeEnvTypeName _hdOmeFunType _hdOmeNamespaceCtor _hdOmeNamespaceNameRoots _hdOmeNamespaceTypeName _hdOmeRelationEnv _hdOmeSortNameRoots _hdOmeSortTypeName
              ( _tlIdesugared,_tlIsFunctionDef,_tlIself,_tlIsmeFunType) =
                  tl_ _tlOmeEnvNameRoots _tlOmeEnvTypeName _tlOmeFunType _tlOmeNamespaceCtor _tlOmeNamespaceNameRoots _tlOmeNamespaceTypeName _tlOmeRelationEnv _tlOmeSortNameRoots _tlOmeSortTypeName
          in  ( _lhsOdesugared,_lhsOsFunctionDef,_lhsOself,_lhsOsmeFunType)))
sem_FunDecls_Nil :: T_FunDecls
sem_FunDecls_Nil =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOdesugared :: (TcM [Core.FunDecl])
              _lhsOsFunctionDef :: (TcM Core.FunctionEnv)
              _lhsOsmeFunType :: MEFunType
              _lhsOself :: FunDecls
              _lhsOdesugared =
                  ({-# LINE 176 "src/KnotSpec/Desugaring.ag" #-}
                   memptyA
                   {-# LINE 3572 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOsFunctionDef =
                  ({-# LINE 603 "src/KnotSpec/Desugaring.ag" #-}
                   memptyA
                   {-# LINE 3577 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOsmeFunType =
                  ({-# LINE 173 "src/KnotSpec/Environment.ag" #-}
                   mempty
                   {-# LINE 3582 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  []
              _lhsOself =
                  _self
          in  ( _lhsOdesugared,_lhsOsFunctionDef,_lhsOself,_lhsOsmeFunType)))
-- Judgement ---------------------------------------------------
-- cata
sem_Judgement :: Judgement ->
                 T_Judgement
sem_Judgement (Judgement _jmtTypeName _jmtTerms) =
    (sem_Judgement_Judgement (sem_TypeName _jmtTypeName) (sem_SymbolicTerms _jmtTerms))
-- semantic domain
type T_Judgement = MEEnvNameRoots ->
                   MEEnvTypeName ->
                   MEFunType ->
                   MENamespaceCtor ->
                   MENamespaceNameRoots ->
                   MENamespaceTypeName ->
                   MERelationEnv ->
                   MESortNameRoots ->
                   MESortTypeName ->
                   ( (TcM Core.Judgement),Judgement)
data Inh_Judgement = Inh_Judgement {meEnvNameRoots_Inh_Judgement :: MEEnvNameRoots,meEnvTypeName_Inh_Judgement :: MEEnvTypeName,meFunType_Inh_Judgement :: MEFunType,meNamespaceCtor_Inh_Judgement :: MENamespaceCtor,meNamespaceNameRoots_Inh_Judgement :: MENamespaceNameRoots,meNamespaceTypeName_Inh_Judgement :: MENamespaceTypeName,meRelationEnv_Inh_Judgement :: MERelationEnv,meSortNameRoots_Inh_Judgement :: MESortNameRoots,meSortTypeName_Inh_Judgement :: MESortTypeName}
data Syn_Judgement = Syn_Judgement {desugared_Syn_Judgement :: (TcM Core.Judgement),self_Syn_Judgement :: Judgement}
wrap_Judgement :: T_Judgement ->
                  Inh_Judgement ->
                  Syn_Judgement
wrap_Judgement sem (Inh_Judgement _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName) =
    (let ( _lhsOdesugared,_lhsOself) = sem _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName
     in  (Syn_Judgement _lhsOdesugared _lhsOself))
sem_Judgement_Judgement :: T_TypeName ->
                           T_SymbolicTerms ->
                           T_Judgement
sem_Judgement_Judgement jmtTypeName_ jmtTerms_ =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOself :: Judgement
              _lhsOdesugared :: (TcM Core.Judgement)
              _jmtTypeNameOmeEnvNameRoots :: MEEnvNameRoots
              _jmtTypeNameOmeEnvTypeName :: MEEnvTypeName
              _jmtTypeNameOmeFunType :: MEFunType
              _jmtTypeNameOmeNamespaceCtor :: MENamespaceCtor
              _jmtTypeNameOmeNamespaceNameRoots :: MENamespaceNameRoots
              _jmtTypeNameOmeNamespaceTypeName :: MENamespaceTypeName
              _jmtTypeNameOmeRelationEnv :: MERelationEnv
              _jmtTypeNameOmeSortNameRoots :: MESortNameRoots
              _jmtTypeNameOmeSortTypeName :: MESortTypeName
              _jmtTermsOmeEnvNameRoots :: MEEnvNameRoots
              _jmtTermsOmeEnvTypeName :: MEEnvTypeName
              _jmtTermsOmeFunType :: MEFunType
              _jmtTermsOmeNamespaceCtor :: MENamespaceCtor
              _jmtTermsOmeNamespaceNameRoots :: MENamespaceNameRoots
              _jmtTermsOmeNamespaceTypeName :: MENamespaceTypeName
              _jmtTermsOmeRelationEnv :: MERelationEnv
              _jmtTermsOmeSortNameRoots :: MESortNameRoots
              _jmtTermsOmeSortTypeName :: MESortTypeName
              _jmtTypeNameIfromTn :: String
              _jmtTypeNameInamespaceTypeName :: (TcM Core.NamespaceTypeName)
              _jmtTypeNameIrelationTypeName :: (TcM Core.RelationTypeName)
              _jmtTypeNameIself :: TypeName
              _jmtTypeNameIsortTypeName :: (TcM Core.SortTypeName)
              _jmtTermsIdesugared :: (TcM [Core.SymbolicTerm])
              _jmtTermsIself :: SymbolicTerms
              _coreMbEnvName =
                  ({-# LINE 413 "src/KnotSpec/Desugaring.ag" #-}
                   do
                     tn@(TN etn) <- Data.Map.lookup _jmtTypeNameIself _lhsImeRelationEnv
                     nrs <- Data.Map.lookup tn _lhsImeEnvNameRoots
                     return (Core.EnvVar (Core.NR . fromNR $ head nrs) "" (Core.ETN etn))
                   {-# LINE 3660 "src/KnotSpec/AG.hs" #-}
                   )
              _desugared =
                  ({-# LINE 418 "src/KnotSpec/Desugaring.ag" #-}
                   Core.Judgement
                     <$> _jmtTypeNameIrelationTypeName
                     <*> pure _coreMbEnvName
                     <*> _jmtTermsIdesugared
                   {-# LINE 3668 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  Judgement _jmtTypeNameIself _jmtTermsIself
              _lhsOself =
                  _self
              _lhsOdesugared =
                  ({-# LINE 409 "src/KnotSpec/Desugaring.ag" #-}
                   _desugared
                   {-# LINE 3677 "src/KnotSpec/AG.hs" #-}
                   )
              _jmtTypeNameOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 3682 "src/KnotSpec/AG.hs" #-}
                   )
              _jmtTypeNameOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 3687 "src/KnotSpec/AG.hs" #-}
                   )
              _jmtTypeNameOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 3692 "src/KnotSpec/AG.hs" #-}
                   )
              _jmtTypeNameOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 3697 "src/KnotSpec/AG.hs" #-}
                   )
              _jmtTypeNameOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 3702 "src/KnotSpec/AG.hs" #-}
                   )
              _jmtTypeNameOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 3707 "src/KnotSpec/AG.hs" #-}
                   )
              _jmtTypeNameOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 3712 "src/KnotSpec/AG.hs" #-}
                   )
              _jmtTypeNameOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 3717 "src/KnotSpec/AG.hs" #-}
                   )
              _jmtTypeNameOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 3722 "src/KnotSpec/AG.hs" #-}
                   )
              _jmtTermsOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 3727 "src/KnotSpec/AG.hs" #-}
                   )
              _jmtTermsOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 3732 "src/KnotSpec/AG.hs" #-}
                   )
              _jmtTermsOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 3737 "src/KnotSpec/AG.hs" #-}
                   )
              _jmtTermsOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 3742 "src/KnotSpec/AG.hs" #-}
                   )
              _jmtTermsOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 3747 "src/KnotSpec/AG.hs" #-}
                   )
              _jmtTermsOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 3752 "src/KnotSpec/AG.hs" #-}
                   )
              _jmtTermsOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 3757 "src/KnotSpec/AG.hs" #-}
                   )
              _jmtTermsOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 3762 "src/KnotSpec/AG.hs" #-}
                   )
              _jmtTermsOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 3767 "src/KnotSpec/AG.hs" #-}
                   )
              ( _jmtTypeNameIfromTn,_jmtTypeNameInamespaceTypeName,_jmtTypeNameIrelationTypeName,_jmtTypeNameIself,_jmtTypeNameIsortTypeName) =
                  jmtTypeName_ _jmtTypeNameOmeEnvNameRoots _jmtTypeNameOmeEnvTypeName _jmtTypeNameOmeFunType _jmtTypeNameOmeNamespaceCtor _jmtTypeNameOmeNamespaceNameRoots _jmtTypeNameOmeNamespaceTypeName _jmtTypeNameOmeRelationEnv _jmtTypeNameOmeSortNameRoots _jmtTypeNameOmeSortTypeName
              ( _jmtTermsIdesugared,_jmtTermsIself) =
                  jmtTerms_ _jmtTermsOmeEnvNameRoots _jmtTermsOmeEnvTypeName _jmtTermsOmeFunType _jmtTermsOmeNamespaceCtor _jmtTermsOmeNamespaceNameRoots _jmtTermsOmeNamespaceTypeName _jmtTermsOmeRelationEnv _jmtTermsOmeSortNameRoots _jmtTermsOmeSortTypeName
          in  ( _lhsOdesugared,_lhsOself)))
-- Judgements --------------------------------------------------
-- cata
sem_Judgements :: Judgements ->
                  T_Judgements
sem_Judgements list =
    (Prelude.foldr sem_Judgements_Cons sem_Judgements_Nil (Prelude.map sem_Judgement list))
-- semantic domain
type T_Judgements = MEEnvNameRoots ->
                    MEEnvTypeName ->
                    MEFunType ->
                    MENamespaceCtor ->
                    MENamespaceNameRoots ->
                    MENamespaceTypeName ->
                    MERelationEnv ->
                    MESortNameRoots ->
                    MESortTypeName ->
                    ( (TcM [Core.Judgement]),Judgements)
data Inh_Judgements = Inh_Judgements {meEnvNameRoots_Inh_Judgements :: MEEnvNameRoots,meEnvTypeName_Inh_Judgements :: MEEnvTypeName,meFunType_Inh_Judgements :: MEFunType,meNamespaceCtor_Inh_Judgements :: MENamespaceCtor,meNamespaceNameRoots_Inh_Judgements :: MENamespaceNameRoots,meNamespaceTypeName_Inh_Judgements :: MENamespaceTypeName,meRelationEnv_Inh_Judgements :: MERelationEnv,meSortNameRoots_Inh_Judgements :: MESortNameRoots,meSortTypeName_Inh_Judgements :: MESortTypeName}
data Syn_Judgements = Syn_Judgements {desugared_Syn_Judgements :: (TcM [Core.Judgement]),self_Syn_Judgements :: Judgements}
wrap_Judgements :: T_Judgements ->
                   Inh_Judgements ->
                   Syn_Judgements
wrap_Judgements sem (Inh_Judgements _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName) =
    (let ( _lhsOdesugared,_lhsOself) = sem _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName
     in  (Syn_Judgements _lhsOdesugared _lhsOself))
sem_Judgements_Cons :: T_Judgement ->
                       T_Judgements ->
                       T_Judgements
sem_Judgements_Cons hd_ tl_ =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOdesugared :: (TcM [Core.Judgement])
              _lhsOself :: Judgements
              _hdOmeEnvNameRoots :: MEEnvNameRoots
              _hdOmeEnvTypeName :: MEEnvTypeName
              _hdOmeFunType :: MEFunType
              _hdOmeNamespaceCtor :: MENamespaceCtor
              _hdOmeNamespaceNameRoots :: MENamespaceNameRoots
              _hdOmeNamespaceTypeName :: MENamespaceTypeName
              _hdOmeRelationEnv :: MERelationEnv
              _hdOmeSortNameRoots :: MESortNameRoots
              _hdOmeSortTypeName :: MESortTypeName
              _tlOmeEnvNameRoots :: MEEnvNameRoots
              _tlOmeEnvTypeName :: MEEnvTypeName
              _tlOmeFunType :: MEFunType
              _tlOmeNamespaceCtor :: MENamespaceCtor
              _tlOmeNamespaceNameRoots :: MENamespaceNameRoots
              _tlOmeNamespaceTypeName :: MENamespaceTypeName
              _tlOmeRelationEnv :: MERelationEnv
              _tlOmeSortNameRoots :: MESortNameRoots
              _tlOmeSortTypeName :: MESortTypeName
              _hdIdesugared :: (TcM Core.Judgement)
              _hdIself :: Judgement
              _tlIdesugared :: (TcM [Core.Judgement])
              _tlIself :: Judgements
              _lhsOdesugared =
                  ({-# LINE 408 "src/KnotSpec/Desugaring.ag" #-}
                   (consA _hdIdesugared _tlIdesugared)
                   {-# LINE 3839 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _hdOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 3848 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 3853 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 3858 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 3863 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 3868 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 3873 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 3878 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 3883 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 3888 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 3893 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 3898 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 3903 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 3908 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 3913 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 3918 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 3923 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 3928 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 3933 "src/KnotSpec/AG.hs" #-}
                   )
              ( _hdIdesugared,_hdIself) =
                  hd_ _hdOmeEnvNameRoots _hdOmeEnvTypeName _hdOmeFunType _hdOmeNamespaceCtor _hdOmeNamespaceNameRoots _hdOmeNamespaceTypeName _hdOmeRelationEnv _hdOmeSortNameRoots _hdOmeSortTypeName
              ( _tlIdesugared,_tlIself) =
                  tl_ _tlOmeEnvNameRoots _tlOmeEnvTypeName _tlOmeFunType _tlOmeNamespaceCtor _tlOmeNamespaceNameRoots _tlOmeNamespaceTypeName _tlOmeRelationEnv _tlOmeSortNameRoots _tlOmeSortTypeName
          in  ( _lhsOdesugared,_lhsOself)))
sem_Judgements_Nil :: T_Judgements
sem_Judgements_Nil =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOdesugared :: (TcM [Core.Judgement])
              _lhsOself :: Judgements
              _lhsOdesugared =
                  ({-# LINE 408 "src/KnotSpec/Desugaring.ag" #-}
                   memptyA
                   {-# LINE 3956 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  []
              _lhsOself =
                  _self
          in  ( _lhsOdesugared,_lhsOself)))
-- MEEnvNameRoots ----------------------------------------------
-- cata
sem_MEEnvNameRoots :: MEEnvNameRoots ->
                      T_MEEnvNameRoots
sem_MEEnvNameRoots m =
    (Data.Map.foldrWithKey sem_MEEnvNameRoots_Entry sem_MEEnvNameRoots_Nil (Data.Map.map sem_NameRoots m))
-- semantic domain
type T_MEEnvNameRoots = MEEnvNameRoots ->
                        MEEnvTypeName ->
                        MEFunType ->
                        MENamespaceCtor ->
                        MENamespaceNameRoots ->
                        MENamespaceTypeName ->
                        MERelationEnv ->
                        MESortNameRoots ->
                        MESortTypeName ->
                        ( MEEnvNameRoots)
data Inh_MEEnvNameRoots = Inh_MEEnvNameRoots {meEnvNameRoots_Inh_MEEnvNameRoots :: MEEnvNameRoots,meEnvTypeName_Inh_MEEnvNameRoots :: MEEnvTypeName,meFunType_Inh_MEEnvNameRoots :: MEFunType,meNamespaceCtor_Inh_MEEnvNameRoots :: MENamespaceCtor,meNamespaceNameRoots_Inh_MEEnvNameRoots :: MENamespaceNameRoots,meNamespaceTypeName_Inh_MEEnvNameRoots :: MENamespaceTypeName,meRelationEnv_Inh_MEEnvNameRoots :: MERelationEnv,meSortNameRoots_Inh_MEEnvNameRoots :: MESortNameRoots,meSortTypeName_Inh_MEEnvNameRoots :: MESortTypeName}
data Syn_MEEnvNameRoots = Syn_MEEnvNameRoots {self_Syn_MEEnvNameRoots :: MEEnvNameRoots}
wrap_MEEnvNameRoots :: T_MEEnvNameRoots ->
                       Inh_MEEnvNameRoots ->
                       Syn_MEEnvNameRoots
wrap_MEEnvNameRoots sem (Inh_MEEnvNameRoots _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName) =
    (let ( _lhsOself) = sem _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName
     in  (Syn_MEEnvNameRoots _lhsOself))
sem_MEEnvNameRoots_Entry :: TypeName ->
                            T_NameRoots ->
                            T_MEEnvNameRoots ->
                            T_MEEnvNameRoots
sem_MEEnvNameRoots_Entry key_ val_ tl_ =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOself :: MEEnvNameRoots
              _tlOmeEnvNameRoots :: MEEnvNameRoots
              _tlOmeEnvTypeName :: MEEnvTypeName
              _tlOmeFunType :: MEFunType
              _tlOmeNamespaceCtor :: MENamespaceCtor
              _tlOmeNamespaceNameRoots :: MENamespaceNameRoots
              _tlOmeNamespaceTypeName :: MENamespaceTypeName
              _tlOmeRelationEnv :: MERelationEnv
              _tlOmeSortNameRoots :: MESortNameRoots
              _tlOmeSortTypeName :: MESortTypeName
              _valIself :: NameRoots
              _tlIself :: MEEnvNameRoots
              _self =
                  Data.Map.insert key_ _valIself _tlIself
              _lhsOself =
                  _self
              _tlOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 4021 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 4026 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 4031 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 4036 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 4041 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 4046 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 4051 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 4056 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 4061 "src/KnotSpec/AG.hs" #-}
                   )
              ( _valIself) =
                  val_
              ( _tlIself) =
                  tl_ _tlOmeEnvNameRoots _tlOmeEnvTypeName _tlOmeFunType _tlOmeNamespaceCtor _tlOmeNamespaceNameRoots _tlOmeNamespaceTypeName _tlOmeRelationEnv _tlOmeSortNameRoots _tlOmeSortTypeName
          in  ( _lhsOself)))
sem_MEEnvNameRoots_Nil :: T_MEEnvNameRoots
sem_MEEnvNameRoots_Nil =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOself :: MEEnvNameRoots
              _self =
                  Data.Map.empty
              _lhsOself =
                  _self
          in  ( _lhsOself)))
-- MEEnvTypeName -----------------------------------------------
-- cata
sem_MEEnvTypeName :: MEEnvTypeName ->
                     T_MEEnvTypeName
sem_MEEnvTypeName m =
    (Data.Map.foldrWithKey sem_MEEnvTypeName_Entry sem_MEEnvTypeName_Nil (Data.Map.map sem_TypeName m))
-- semantic domain
type T_MEEnvTypeName = MEEnvNameRoots ->
                       MEEnvTypeName ->
                       MEFunType ->
                       MENamespaceCtor ->
                       MENamespaceNameRoots ->
                       MENamespaceTypeName ->
                       MERelationEnv ->
                       MESortNameRoots ->
                       MESortTypeName ->
                       ( MEEnvTypeName)
data Inh_MEEnvTypeName = Inh_MEEnvTypeName {meEnvNameRoots_Inh_MEEnvTypeName :: MEEnvNameRoots,meEnvTypeName_Inh_MEEnvTypeName :: MEEnvTypeName,meFunType_Inh_MEEnvTypeName :: MEFunType,meNamespaceCtor_Inh_MEEnvTypeName :: MENamespaceCtor,meNamespaceNameRoots_Inh_MEEnvTypeName :: MENamespaceNameRoots,meNamespaceTypeName_Inh_MEEnvTypeName :: MENamespaceTypeName,meRelationEnv_Inh_MEEnvTypeName :: MERelationEnv,meSortNameRoots_Inh_MEEnvTypeName :: MESortNameRoots,meSortTypeName_Inh_MEEnvTypeName :: MESortTypeName}
data Syn_MEEnvTypeName = Syn_MEEnvTypeName {self_Syn_MEEnvTypeName :: MEEnvTypeName}
wrap_MEEnvTypeName :: T_MEEnvTypeName ->
                      Inh_MEEnvTypeName ->
                      Syn_MEEnvTypeName
wrap_MEEnvTypeName sem (Inh_MEEnvTypeName _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName) =
    (let ( _lhsOself) = sem _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName
     in  (Syn_MEEnvTypeName _lhsOself))
sem_MEEnvTypeName_Entry :: NameRoot ->
                           T_TypeName ->
                           T_MEEnvTypeName ->
                           T_MEEnvTypeName
sem_MEEnvTypeName_Entry key_ val_ tl_ =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOself :: MEEnvTypeName
              _valOmeEnvNameRoots :: MEEnvNameRoots
              _valOmeEnvTypeName :: MEEnvTypeName
              _valOmeFunType :: MEFunType
              _valOmeNamespaceCtor :: MENamespaceCtor
              _valOmeNamespaceNameRoots :: MENamespaceNameRoots
              _valOmeNamespaceTypeName :: MENamespaceTypeName
              _valOmeRelationEnv :: MERelationEnv
              _valOmeSortNameRoots :: MESortNameRoots
              _valOmeSortTypeName :: MESortTypeName
              _tlOmeEnvNameRoots :: MEEnvNameRoots
              _tlOmeEnvTypeName :: MEEnvTypeName
              _tlOmeFunType :: MEFunType
              _tlOmeNamespaceCtor :: MENamespaceCtor
              _tlOmeNamespaceNameRoots :: MENamespaceNameRoots
              _tlOmeNamespaceTypeName :: MENamespaceTypeName
              _tlOmeRelationEnv :: MERelationEnv
              _tlOmeSortNameRoots :: MESortNameRoots
              _tlOmeSortTypeName :: MESortTypeName
              _valIfromTn :: String
              _valInamespaceTypeName :: (TcM Core.NamespaceTypeName)
              _valIrelationTypeName :: (TcM Core.RelationTypeName)
              _valIself :: TypeName
              _valIsortTypeName :: (TcM Core.SortTypeName)
              _tlIself :: MEEnvTypeName
              _self =
                  Data.Map.insert key_ _valIself _tlIself
              _lhsOself =
                  _self
              _valOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 4156 "src/KnotSpec/AG.hs" #-}
                   )
              _valOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 4161 "src/KnotSpec/AG.hs" #-}
                   )
              _valOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 4166 "src/KnotSpec/AG.hs" #-}
                   )
              _valOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 4171 "src/KnotSpec/AG.hs" #-}
                   )
              _valOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 4176 "src/KnotSpec/AG.hs" #-}
                   )
              _valOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 4181 "src/KnotSpec/AG.hs" #-}
                   )
              _valOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 4186 "src/KnotSpec/AG.hs" #-}
                   )
              _valOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 4191 "src/KnotSpec/AG.hs" #-}
                   )
              _valOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 4196 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 4201 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 4206 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 4211 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 4216 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 4221 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 4226 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 4231 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 4236 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 4241 "src/KnotSpec/AG.hs" #-}
                   )
              ( _valIfromTn,_valInamespaceTypeName,_valIrelationTypeName,_valIself,_valIsortTypeName) =
                  val_ _valOmeEnvNameRoots _valOmeEnvTypeName _valOmeFunType _valOmeNamespaceCtor _valOmeNamespaceNameRoots _valOmeNamespaceTypeName _valOmeRelationEnv _valOmeSortNameRoots _valOmeSortTypeName
              ( _tlIself) =
                  tl_ _tlOmeEnvNameRoots _tlOmeEnvTypeName _tlOmeFunType _tlOmeNamespaceCtor _tlOmeNamespaceNameRoots _tlOmeNamespaceTypeName _tlOmeRelationEnv _tlOmeSortNameRoots _tlOmeSortTypeName
          in  ( _lhsOself)))
sem_MEEnvTypeName_Nil :: T_MEEnvTypeName
sem_MEEnvTypeName_Nil =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOself :: MEEnvTypeName
              _self =
                  Data.Map.empty
              _lhsOself =
                  _self
          in  ( _lhsOself)))
-- MEFunType ---------------------------------------------------
-- cata
sem_MEFunType :: MEFunType ->
                 T_MEFunType
sem_MEFunType m =
    (Data.Map.foldrWithKey sem_MEFunType_Entry sem_MEFunType_Nil m)
-- semantic domain
type T_MEFunType = ( MEFunType)
data Inh_MEFunType = Inh_MEFunType {}
data Syn_MEFunType = Syn_MEFunType {self_Syn_MEFunType :: MEFunType}
wrap_MEFunType :: T_MEFunType ->
                  Inh_MEFunType ->
                  Syn_MEFunType
wrap_MEFunType sem (Inh_MEFunType) =
    (let ( _lhsOself) = sem
     in  (Syn_MEFunType _lhsOself))
sem_MEFunType_Entry :: FunName ->
                       ((TypeName,TypeNames)) ->
                       T_MEFunType ->
                       T_MEFunType
sem_MEFunType_Entry key_ val_ tl_ =
    (let _lhsOself :: MEFunType
         _tlIself :: MEFunType
         _self =
             Data.Map.insert key_ val_ _tlIself
         _lhsOself =
             _self
         ( _tlIself) =
             tl_
     in  ( _lhsOself))
sem_MEFunType_Nil :: T_MEFunType
sem_MEFunType_Nil =
    (let _lhsOself :: MEFunType
         _self =
             Data.Map.empty
         _lhsOself =
             _self
     in  ( _lhsOself))
-- MENamespaceCtor ---------------------------------------------
-- cata
sem_MENamespaceCtor :: MENamespaceCtor ->
                       T_MENamespaceCtor
sem_MENamespaceCtor m =
    (Data.Map.foldrWithKey sem_MENamespaceCtor_Entry sem_MENamespaceCtor_Nil m)
-- semantic domain
type T_MENamespaceCtor = MEEnvNameRoots ->
                         MEEnvTypeName ->
                         MEFunType ->
                         MENamespaceCtor ->
                         MENamespaceNameRoots ->
                         MENamespaceTypeName ->
                         MERelationEnv ->
                         MESortNameRoots ->
                         MESortTypeName ->
                         ( MENamespaceCtor)
data Inh_MENamespaceCtor = Inh_MENamespaceCtor {meEnvNameRoots_Inh_MENamespaceCtor :: MEEnvNameRoots,meEnvTypeName_Inh_MENamespaceCtor :: MEEnvTypeName,meFunType_Inh_MENamespaceCtor :: MEFunType,meNamespaceCtor_Inh_MENamespaceCtor :: MENamespaceCtor,meNamespaceNameRoots_Inh_MENamespaceCtor :: MENamespaceNameRoots,meNamespaceTypeName_Inh_MENamespaceCtor :: MENamespaceTypeName,meRelationEnv_Inh_MENamespaceCtor :: MERelationEnv,meSortNameRoots_Inh_MENamespaceCtor :: MESortNameRoots,meSortTypeName_Inh_MENamespaceCtor :: MESortTypeName}
data Syn_MENamespaceCtor = Syn_MENamespaceCtor {self_Syn_MENamespaceCtor :: MENamespaceCtor}
wrap_MENamespaceCtor :: T_MENamespaceCtor ->
                        Inh_MENamespaceCtor ->
                        Syn_MENamespaceCtor
wrap_MENamespaceCtor sem (Inh_MENamespaceCtor _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName) =
    (let ( _lhsOself) = sem _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName
     in  (Syn_MENamespaceCtor _lhsOself))
sem_MENamespaceCtor_Entry :: TypeName ->
                             ((TypeName,CtorName)) ->
                             T_MENamespaceCtor ->
                             T_MENamespaceCtor
sem_MENamespaceCtor_Entry key_ val_ tl_ =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOself :: MENamespaceCtor
              _tlOmeEnvNameRoots :: MEEnvNameRoots
              _tlOmeEnvTypeName :: MEEnvTypeName
              _tlOmeFunType :: MEFunType
              _tlOmeNamespaceCtor :: MENamespaceCtor
              _tlOmeNamespaceNameRoots :: MENamespaceNameRoots
              _tlOmeNamespaceTypeName :: MENamespaceTypeName
              _tlOmeRelationEnv :: MERelationEnv
              _tlOmeSortNameRoots :: MESortNameRoots
              _tlOmeSortTypeName :: MESortTypeName
              _tlIself :: MENamespaceCtor
              _self =
                  Data.Map.insert key_ val_ _tlIself
              _lhsOself =
                  _self
              _tlOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 4360 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 4365 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 4370 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 4375 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 4380 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 4385 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 4390 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 4395 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 4400 "src/KnotSpec/AG.hs" #-}
                   )
              ( _tlIself) =
                  tl_ _tlOmeEnvNameRoots _tlOmeEnvTypeName _tlOmeFunType _tlOmeNamespaceCtor _tlOmeNamespaceNameRoots _tlOmeNamespaceTypeName _tlOmeRelationEnv _tlOmeSortNameRoots _tlOmeSortTypeName
          in  ( _lhsOself)))
sem_MENamespaceCtor_Nil :: T_MENamespaceCtor
sem_MENamespaceCtor_Nil =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOself :: MENamespaceCtor
              _self =
                  Data.Map.empty
              _lhsOself =
                  _self
          in  ( _lhsOself)))
-- MENamespaceNameRoots ----------------------------------------
-- cata
sem_MENamespaceNameRoots :: MENamespaceNameRoots ->
                            T_MENamespaceNameRoots
sem_MENamespaceNameRoots m =
    (Data.Map.foldrWithKey sem_MENamespaceNameRoots_Entry sem_MENamespaceNameRoots_Nil (Data.Map.map sem_NameRoots m))
-- semantic domain
type T_MENamespaceNameRoots = MEEnvNameRoots ->
                              MEEnvTypeName ->
                              MEFunType ->
                              MENamespaceCtor ->
                              MENamespaceNameRoots ->
                              MENamespaceTypeName ->
                              MERelationEnv ->
                              MESortNameRoots ->
                              MESortTypeName ->
                              ( MENamespaceNameRoots)
data Inh_MENamespaceNameRoots = Inh_MENamespaceNameRoots {meEnvNameRoots_Inh_MENamespaceNameRoots :: MEEnvNameRoots,meEnvTypeName_Inh_MENamespaceNameRoots :: MEEnvTypeName,meFunType_Inh_MENamespaceNameRoots :: MEFunType,meNamespaceCtor_Inh_MENamespaceNameRoots :: MENamespaceCtor,meNamespaceNameRoots_Inh_MENamespaceNameRoots :: MENamespaceNameRoots,meNamespaceTypeName_Inh_MENamespaceNameRoots :: MENamespaceTypeName,meRelationEnv_Inh_MENamespaceNameRoots :: MERelationEnv,meSortNameRoots_Inh_MENamespaceNameRoots :: MESortNameRoots,meSortTypeName_Inh_MENamespaceNameRoots :: MESortTypeName}
data Syn_MENamespaceNameRoots = Syn_MENamespaceNameRoots {self_Syn_MENamespaceNameRoots :: MENamespaceNameRoots}
wrap_MENamespaceNameRoots :: T_MENamespaceNameRoots ->
                             Inh_MENamespaceNameRoots ->
                             Syn_MENamespaceNameRoots
wrap_MENamespaceNameRoots sem (Inh_MENamespaceNameRoots _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName) =
    (let ( _lhsOself) = sem _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName
     in  (Syn_MENamespaceNameRoots _lhsOself))
sem_MENamespaceNameRoots_Entry :: TypeName ->
                                  T_NameRoots ->
                                  T_MENamespaceNameRoots ->
                                  T_MENamespaceNameRoots
sem_MENamespaceNameRoots_Entry key_ val_ tl_ =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOself :: MENamespaceNameRoots
              _tlOmeEnvNameRoots :: MEEnvNameRoots
              _tlOmeEnvTypeName :: MEEnvTypeName
              _tlOmeFunType :: MEFunType
              _tlOmeNamespaceCtor :: MENamespaceCtor
              _tlOmeNamespaceNameRoots :: MENamespaceNameRoots
              _tlOmeNamespaceTypeName :: MENamespaceTypeName
              _tlOmeRelationEnv :: MERelationEnv
              _tlOmeSortNameRoots :: MESortNameRoots
              _tlOmeSortTypeName :: MESortTypeName
              _valIself :: NameRoots
              _tlIself :: MENamespaceNameRoots
              _self =
                  Data.Map.insert key_ _valIself _tlIself
              _lhsOself =
                  _self
              _tlOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 4480 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 4485 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 4490 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 4495 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 4500 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 4505 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 4510 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 4515 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 4520 "src/KnotSpec/AG.hs" #-}
                   )
              ( _valIself) =
                  val_
              ( _tlIself) =
                  tl_ _tlOmeEnvNameRoots _tlOmeEnvTypeName _tlOmeFunType _tlOmeNamespaceCtor _tlOmeNamespaceNameRoots _tlOmeNamespaceTypeName _tlOmeRelationEnv _tlOmeSortNameRoots _tlOmeSortTypeName
          in  ( _lhsOself)))
sem_MENamespaceNameRoots_Nil :: T_MENamespaceNameRoots
sem_MENamespaceNameRoots_Nil =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOself :: MENamespaceNameRoots
              _self =
                  Data.Map.empty
              _lhsOself =
                  _self
          in  ( _lhsOself)))
-- MENamespaceTypeName -----------------------------------------
-- cata
sem_MENamespaceTypeName :: MENamespaceTypeName ->
                           T_MENamespaceTypeName
sem_MENamespaceTypeName m =
    (Data.Map.foldrWithKey sem_MENamespaceTypeName_Entry sem_MENamespaceTypeName_Nil (Data.Map.map sem_TypeName m))
-- semantic domain
type T_MENamespaceTypeName = MEEnvNameRoots ->
                             MEEnvTypeName ->
                             MEFunType ->
                             MENamespaceCtor ->
                             MENamespaceNameRoots ->
                             MENamespaceTypeName ->
                             MERelationEnv ->
                             MESortNameRoots ->
                             MESortTypeName ->
                             ( MENamespaceTypeName)
data Inh_MENamespaceTypeName = Inh_MENamespaceTypeName {meEnvNameRoots_Inh_MENamespaceTypeName :: MEEnvNameRoots,meEnvTypeName_Inh_MENamespaceTypeName :: MEEnvTypeName,meFunType_Inh_MENamespaceTypeName :: MEFunType,meNamespaceCtor_Inh_MENamespaceTypeName :: MENamespaceCtor,meNamespaceNameRoots_Inh_MENamespaceTypeName :: MENamespaceNameRoots,meNamespaceTypeName_Inh_MENamespaceTypeName :: MENamespaceTypeName,meRelationEnv_Inh_MENamespaceTypeName :: MERelationEnv,meSortNameRoots_Inh_MENamespaceTypeName :: MESortNameRoots,meSortTypeName_Inh_MENamespaceTypeName :: MESortTypeName}
data Syn_MENamespaceTypeName = Syn_MENamespaceTypeName {self_Syn_MENamespaceTypeName :: MENamespaceTypeName}
wrap_MENamespaceTypeName :: T_MENamespaceTypeName ->
                            Inh_MENamespaceTypeName ->
                            Syn_MENamespaceTypeName
wrap_MENamespaceTypeName sem (Inh_MENamespaceTypeName _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName) =
    (let ( _lhsOself) = sem _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName
     in  (Syn_MENamespaceTypeName _lhsOself))
sem_MENamespaceTypeName_Entry :: NameRoot ->
                                 T_TypeName ->
                                 T_MENamespaceTypeName ->
                                 T_MENamespaceTypeName
sem_MENamespaceTypeName_Entry key_ val_ tl_ =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOself :: MENamespaceTypeName
              _valOmeEnvNameRoots :: MEEnvNameRoots
              _valOmeEnvTypeName :: MEEnvTypeName
              _valOmeFunType :: MEFunType
              _valOmeNamespaceCtor :: MENamespaceCtor
              _valOmeNamespaceNameRoots :: MENamespaceNameRoots
              _valOmeNamespaceTypeName :: MENamespaceTypeName
              _valOmeRelationEnv :: MERelationEnv
              _valOmeSortNameRoots :: MESortNameRoots
              _valOmeSortTypeName :: MESortTypeName
              _tlOmeEnvNameRoots :: MEEnvNameRoots
              _tlOmeEnvTypeName :: MEEnvTypeName
              _tlOmeFunType :: MEFunType
              _tlOmeNamespaceCtor :: MENamespaceCtor
              _tlOmeNamespaceNameRoots :: MENamespaceNameRoots
              _tlOmeNamespaceTypeName :: MENamespaceTypeName
              _tlOmeRelationEnv :: MERelationEnv
              _tlOmeSortNameRoots :: MESortNameRoots
              _tlOmeSortTypeName :: MESortTypeName
              _valIfromTn :: String
              _valInamespaceTypeName :: (TcM Core.NamespaceTypeName)
              _valIrelationTypeName :: (TcM Core.RelationTypeName)
              _valIself :: TypeName
              _valIsortTypeName :: (TcM Core.SortTypeName)
              _tlIself :: MENamespaceTypeName
              _self =
                  Data.Map.insert key_ _valIself _tlIself
              _lhsOself =
                  _self
              _valOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 4615 "src/KnotSpec/AG.hs" #-}
                   )
              _valOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 4620 "src/KnotSpec/AG.hs" #-}
                   )
              _valOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 4625 "src/KnotSpec/AG.hs" #-}
                   )
              _valOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 4630 "src/KnotSpec/AG.hs" #-}
                   )
              _valOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 4635 "src/KnotSpec/AG.hs" #-}
                   )
              _valOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 4640 "src/KnotSpec/AG.hs" #-}
                   )
              _valOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 4645 "src/KnotSpec/AG.hs" #-}
                   )
              _valOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 4650 "src/KnotSpec/AG.hs" #-}
                   )
              _valOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 4655 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 4660 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 4665 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 4670 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 4675 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 4680 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 4685 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 4690 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 4695 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 4700 "src/KnotSpec/AG.hs" #-}
                   )
              ( _valIfromTn,_valInamespaceTypeName,_valIrelationTypeName,_valIself,_valIsortTypeName) =
                  val_ _valOmeEnvNameRoots _valOmeEnvTypeName _valOmeFunType _valOmeNamespaceCtor _valOmeNamespaceNameRoots _valOmeNamespaceTypeName _valOmeRelationEnv _valOmeSortNameRoots _valOmeSortTypeName
              ( _tlIself) =
                  tl_ _tlOmeEnvNameRoots _tlOmeEnvTypeName _tlOmeFunType _tlOmeNamespaceCtor _tlOmeNamespaceNameRoots _tlOmeNamespaceTypeName _tlOmeRelationEnv _tlOmeSortNameRoots _tlOmeSortTypeName
          in  ( _lhsOself)))
sem_MENamespaceTypeName_Nil :: T_MENamespaceTypeName
sem_MENamespaceTypeName_Nil =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOself :: MENamespaceTypeName
              _self =
                  Data.Map.empty
              _lhsOself =
                  _self
          in  ( _lhsOself)))
-- MERelationEnv -----------------------------------------------
-- cata
sem_MERelationEnv :: MERelationEnv ->
                     T_MERelationEnv
sem_MERelationEnv m =
    (Data.Map.foldrWithKey sem_MERelationEnv_Entry sem_MERelationEnv_Nil m)
-- semantic domain
type T_MERelationEnv = MEEnvNameRoots ->
                       MEEnvTypeName ->
                       MEFunType ->
                       MENamespaceCtor ->
                       MENamespaceNameRoots ->
                       MENamespaceTypeName ->
                       MERelationEnv ->
                       MESortNameRoots ->
                       MESortTypeName ->
                       ( MERelationEnv)
data Inh_MERelationEnv = Inh_MERelationEnv {meEnvNameRoots_Inh_MERelationEnv :: MEEnvNameRoots,meEnvTypeName_Inh_MERelationEnv :: MEEnvTypeName,meFunType_Inh_MERelationEnv :: MEFunType,meNamespaceCtor_Inh_MERelationEnv :: MENamespaceCtor,meNamespaceNameRoots_Inh_MERelationEnv :: MENamespaceNameRoots,meNamespaceTypeName_Inh_MERelationEnv :: MENamespaceTypeName,meRelationEnv_Inh_MERelationEnv :: MERelationEnv,meSortNameRoots_Inh_MERelationEnv :: MESortNameRoots,meSortTypeName_Inh_MERelationEnv :: MESortTypeName}
data Syn_MERelationEnv = Syn_MERelationEnv {self_Syn_MERelationEnv :: MERelationEnv}
wrap_MERelationEnv :: T_MERelationEnv ->
                      Inh_MERelationEnv ->
                      Syn_MERelationEnv
wrap_MERelationEnv sem (Inh_MERelationEnv _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName) =
    (let ( _lhsOself) = sem _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName
     in  (Syn_MERelationEnv _lhsOself))
sem_MERelationEnv_Entry :: TypeName ->
                           TypeName ->
                           T_MERelationEnv ->
                           T_MERelationEnv
sem_MERelationEnv_Entry key_ val_ tl_ =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOself :: MERelationEnv
              _tlOmeEnvNameRoots :: MEEnvNameRoots
              _tlOmeEnvTypeName :: MEEnvTypeName
              _tlOmeFunType :: MEFunType
              _tlOmeNamespaceCtor :: MENamespaceCtor
              _tlOmeNamespaceNameRoots :: MENamespaceNameRoots
              _tlOmeNamespaceTypeName :: MENamespaceTypeName
              _tlOmeRelationEnv :: MERelationEnv
              _tlOmeSortNameRoots :: MESortNameRoots
              _tlOmeSortTypeName :: MESortTypeName
              _tlIself :: MERelationEnv
              _self =
                  Data.Map.insert key_ val_ _tlIself
              _lhsOself =
                  _self
              _tlOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 4781 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 4786 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 4791 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 4796 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 4801 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 4806 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 4811 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 4816 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 4821 "src/KnotSpec/AG.hs" #-}
                   )
              ( _tlIself) =
                  tl_ _tlOmeEnvNameRoots _tlOmeEnvTypeName _tlOmeFunType _tlOmeNamespaceCtor _tlOmeNamespaceNameRoots _tlOmeNamespaceTypeName _tlOmeRelationEnv _tlOmeSortNameRoots _tlOmeSortTypeName
          in  ( _lhsOself)))
sem_MERelationEnv_Nil :: T_MERelationEnv
sem_MERelationEnv_Nil =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOself :: MERelationEnv
              _self =
                  Data.Map.empty
              _lhsOself =
                  _self
          in  ( _lhsOself)))
-- MESortNameRoots ---------------------------------------------
-- cata
sem_MESortNameRoots :: MESortNameRoots ->
                       T_MESortNameRoots
sem_MESortNameRoots m =
    (Data.Map.foldrWithKey sem_MESortNameRoots_Entry sem_MESortNameRoots_Nil (Data.Map.map sem_NameRoots m))
-- semantic domain
type T_MESortNameRoots = MEEnvNameRoots ->
                         MEEnvTypeName ->
                         MEFunType ->
                         MENamespaceCtor ->
                         MENamespaceNameRoots ->
                         MENamespaceTypeName ->
                         MERelationEnv ->
                         MESortNameRoots ->
                         MESortTypeName ->
                         ( MESortNameRoots)
data Inh_MESortNameRoots = Inh_MESortNameRoots {meEnvNameRoots_Inh_MESortNameRoots :: MEEnvNameRoots,meEnvTypeName_Inh_MESortNameRoots :: MEEnvTypeName,meFunType_Inh_MESortNameRoots :: MEFunType,meNamespaceCtor_Inh_MESortNameRoots :: MENamespaceCtor,meNamespaceNameRoots_Inh_MESortNameRoots :: MENamespaceNameRoots,meNamespaceTypeName_Inh_MESortNameRoots :: MENamespaceTypeName,meRelationEnv_Inh_MESortNameRoots :: MERelationEnv,meSortNameRoots_Inh_MESortNameRoots :: MESortNameRoots,meSortTypeName_Inh_MESortNameRoots :: MESortTypeName}
data Syn_MESortNameRoots = Syn_MESortNameRoots {self_Syn_MESortNameRoots :: MESortNameRoots}
wrap_MESortNameRoots :: T_MESortNameRoots ->
                        Inh_MESortNameRoots ->
                        Syn_MESortNameRoots
wrap_MESortNameRoots sem (Inh_MESortNameRoots _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName) =
    (let ( _lhsOself) = sem _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName
     in  (Syn_MESortNameRoots _lhsOself))
sem_MESortNameRoots_Entry :: TypeName ->
                             T_NameRoots ->
                             T_MESortNameRoots ->
                             T_MESortNameRoots
sem_MESortNameRoots_Entry key_ val_ tl_ =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOself :: MESortNameRoots
              _tlOmeEnvNameRoots :: MEEnvNameRoots
              _tlOmeEnvTypeName :: MEEnvTypeName
              _tlOmeFunType :: MEFunType
              _tlOmeNamespaceCtor :: MENamespaceCtor
              _tlOmeNamespaceNameRoots :: MENamespaceNameRoots
              _tlOmeNamespaceTypeName :: MENamespaceTypeName
              _tlOmeRelationEnv :: MERelationEnv
              _tlOmeSortNameRoots :: MESortNameRoots
              _tlOmeSortTypeName :: MESortTypeName
              _valIself :: NameRoots
              _tlIself :: MESortNameRoots
              _self =
                  Data.Map.insert key_ _valIself _tlIself
              _lhsOself =
                  _self
              _tlOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 4901 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 4906 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 4911 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 4916 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 4921 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 4926 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 4931 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 4936 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 4941 "src/KnotSpec/AG.hs" #-}
                   )
              ( _valIself) =
                  val_
              ( _tlIself) =
                  tl_ _tlOmeEnvNameRoots _tlOmeEnvTypeName _tlOmeFunType _tlOmeNamespaceCtor _tlOmeNamespaceNameRoots _tlOmeNamespaceTypeName _tlOmeRelationEnv _tlOmeSortNameRoots _tlOmeSortTypeName
          in  ( _lhsOself)))
sem_MESortNameRoots_Nil :: T_MESortNameRoots
sem_MESortNameRoots_Nil =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOself :: MESortNameRoots
              _self =
                  Data.Map.empty
              _lhsOself =
                  _self
          in  ( _lhsOself)))
-- MESortTypeName ----------------------------------------------
-- cata
sem_MESortTypeName :: MESortTypeName ->
                      T_MESortTypeName
sem_MESortTypeName m =
    (Data.Map.foldrWithKey sem_MESortTypeName_Entry sem_MESortTypeName_Nil (Data.Map.map sem_TypeName m))
-- semantic domain
type T_MESortTypeName = MEEnvNameRoots ->
                        MEEnvTypeName ->
                        MEFunType ->
                        MENamespaceCtor ->
                        MENamespaceNameRoots ->
                        MENamespaceTypeName ->
                        MERelationEnv ->
                        MESortNameRoots ->
                        MESortTypeName ->
                        ( MESortTypeName)
data Inh_MESortTypeName = Inh_MESortTypeName {meEnvNameRoots_Inh_MESortTypeName :: MEEnvNameRoots,meEnvTypeName_Inh_MESortTypeName :: MEEnvTypeName,meFunType_Inh_MESortTypeName :: MEFunType,meNamespaceCtor_Inh_MESortTypeName :: MENamespaceCtor,meNamespaceNameRoots_Inh_MESortTypeName :: MENamespaceNameRoots,meNamespaceTypeName_Inh_MESortTypeName :: MENamespaceTypeName,meRelationEnv_Inh_MESortTypeName :: MERelationEnv,meSortNameRoots_Inh_MESortTypeName :: MESortNameRoots,meSortTypeName_Inh_MESortTypeName :: MESortTypeName}
data Syn_MESortTypeName = Syn_MESortTypeName {self_Syn_MESortTypeName :: MESortTypeName}
wrap_MESortTypeName :: T_MESortTypeName ->
                       Inh_MESortTypeName ->
                       Syn_MESortTypeName
wrap_MESortTypeName sem (Inh_MESortTypeName _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName) =
    (let ( _lhsOself) = sem _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName
     in  (Syn_MESortTypeName _lhsOself))
sem_MESortTypeName_Entry :: NameRoot ->
                            T_TypeName ->
                            T_MESortTypeName ->
                            T_MESortTypeName
sem_MESortTypeName_Entry key_ val_ tl_ =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOself :: MESortTypeName
              _valOmeEnvNameRoots :: MEEnvNameRoots
              _valOmeEnvTypeName :: MEEnvTypeName
              _valOmeFunType :: MEFunType
              _valOmeNamespaceCtor :: MENamespaceCtor
              _valOmeNamespaceNameRoots :: MENamespaceNameRoots
              _valOmeNamespaceTypeName :: MENamespaceTypeName
              _valOmeRelationEnv :: MERelationEnv
              _valOmeSortNameRoots :: MESortNameRoots
              _valOmeSortTypeName :: MESortTypeName
              _tlOmeEnvNameRoots :: MEEnvNameRoots
              _tlOmeEnvTypeName :: MEEnvTypeName
              _tlOmeFunType :: MEFunType
              _tlOmeNamespaceCtor :: MENamespaceCtor
              _tlOmeNamespaceNameRoots :: MENamespaceNameRoots
              _tlOmeNamespaceTypeName :: MENamespaceTypeName
              _tlOmeRelationEnv :: MERelationEnv
              _tlOmeSortNameRoots :: MESortNameRoots
              _tlOmeSortTypeName :: MESortTypeName
              _valIfromTn :: String
              _valInamespaceTypeName :: (TcM Core.NamespaceTypeName)
              _valIrelationTypeName :: (TcM Core.RelationTypeName)
              _valIself :: TypeName
              _valIsortTypeName :: (TcM Core.SortTypeName)
              _tlIself :: MESortTypeName
              _self =
                  Data.Map.insert key_ _valIself _tlIself
              _lhsOself =
                  _self
              _valOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 5036 "src/KnotSpec/AG.hs" #-}
                   )
              _valOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 5041 "src/KnotSpec/AG.hs" #-}
                   )
              _valOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 5046 "src/KnotSpec/AG.hs" #-}
                   )
              _valOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 5051 "src/KnotSpec/AG.hs" #-}
                   )
              _valOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 5056 "src/KnotSpec/AG.hs" #-}
                   )
              _valOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 5061 "src/KnotSpec/AG.hs" #-}
                   )
              _valOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 5066 "src/KnotSpec/AG.hs" #-}
                   )
              _valOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 5071 "src/KnotSpec/AG.hs" #-}
                   )
              _valOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 5076 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 5081 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 5086 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 5091 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 5096 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 5101 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 5106 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 5111 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 5116 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 5121 "src/KnotSpec/AG.hs" #-}
                   )
              ( _valIfromTn,_valInamespaceTypeName,_valIrelationTypeName,_valIself,_valIsortTypeName) =
                  val_ _valOmeEnvNameRoots _valOmeEnvTypeName _valOmeFunType _valOmeNamespaceCtor _valOmeNamespaceNameRoots _valOmeNamespaceTypeName _valOmeRelationEnv _valOmeSortNameRoots _valOmeSortTypeName
              ( _tlIself) =
                  tl_ _tlOmeEnvNameRoots _tlOmeEnvTypeName _tlOmeFunType _tlOmeNamespaceCtor _tlOmeNamespaceNameRoots _tlOmeNamespaceTypeName _tlOmeRelationEnv _tlOmeSortNameRoots _tlOmeSortTypeName
          in  ( _lhsOself)))
sem_MESortTypeName_Nil :: T_MESortTypeName
sem_MESortTypeName_Nil =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOself :: MESortTypeName
              _self =
                  Data.Map.empty
              _lhsOself =
                  _self
          in  ( _lhsOself)))
-- MbString ----------------------------------------------------
-- cata
sem_MbString :: MbString ->
                T_MbString
sem_MbString (Prelude.Just x) =
    (sem_MbString_Just x)
sem_MbString Prelude.Nothing =
    sem_MbString_Nothing
-- semantic domain
type T_MbString = ( MbString)
data Inh_MbString = Inh_MbString {}
data Syn_MbString = Syn_MbString {self_Syn_MbString :: MbString}
wrap_MbString :: T_MbString ->
                 Inh_MbString ->
                 Syn_MbString
wrap_MbString sem (Inh_MbString) =
    (let ( _lhsOself) = sem
     in  (Syn_MbString _lhsOself))
sem_MbString_Just :: String ->
                     T_MbString
sem_MbString_Just just_ =
    (let _lhsOself :: MbString
         _self =
             Just just_
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_MbString_Nothing :: T_MbString
sem_MbString_Nothing =
    (let _lhsOself :: MbString
         _self =
             Nothing
         _lhsOself =
             _self
     in  ( _lhsOself))
-- MbTypeName --------------------------------------------------
-- cata
sem_MbTypeName :: MbTypeName ->
                  T_MbTypeName
sem_MbTypeName (Prelude.Just x) =
    (sem_MbTypeName_Just (sem_TypeName x))
sem_MbTypeName Prelude.Nothing =
    sem_MbTypeName_Nothing
-- semantic domain
type T_MbTypeName = MEEnvNameRoots ->
                    MEEnvTypeName ->
                    MEFunType ->
                    MENamespaceCtor ->
                    MENamespaceNameRoots ->
                    MENamespaceTypeName ->
                    MERelationEnv ->
                    MESortNameRoots ->
                    MESortTypeName ->
                    ( MbTypeName)
data Inh_MbTypeName = Inh_MbTypeName {meEnvNameRoots_Inh_MbTypeName :: MEEnvNameRoots,meEnvTypeName_Inh_MbTypeName :: MEEnvTypeName,meFunType_Inh_MbTypeName :: MEFunType,meNamespaceCtor_Inh_MbTypeName :: MENamespaceCtor,meNamespaceNameRoots_Inh_MbTypeName :: MENamespaceNameRoots,meNamespaceTypeName_Inh_MbTypeName :: MENamespaceTypeName,meRelationEnv_Inh_MbTypeName :: MERelationEnv,meSortNameRoots_Inh_MbTypeName :: MESortNameRoots,meSortTypeName_Inh_MbTypeName :: MESortTypeName}
data Syn_MbTypeName = Syn_MbTypeName {self_Syn_MbTypeName :: MbTypeName}
wrap_MbTypeName :: T_MbTypeName ->
                   Inh_MbTypeName ->
                   Syn_MbTypeName
wrap_MbTypeName sem (Inh_MbTypeName _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName) =
    (let ( _lhsOself) = sem _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName
     in  (Syn_MbTypeName _lhsOself))
sem_MbTypeName_Just :: T_TypeName ->
                       T_MbTypeName
sem_MbTypeName_Just just_ =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOself :: MbTypeName
              _justOmeEnvNameRoots :: MEEnvNameRoots
              _justOmeEnvTypeName :: MEEnvTypeName
              _justOmeFunType :: MEFunType
              _justOmeNamespaceCtor :: MENamespaceCtor
              _justOmeNamespaceNameRoots :: MENamespaceNameRoots
              _justOmeNamespaceTypeName :: MENamespaceTypeName
              _justOmeRelationEnv :: MERelationEnv
              _justOmeSortNameRoots :: MESortNameRoots
              _justOmeSortTypeName :: MESortTypeName
              _justIfromTn :: String
              _justInamespaceTypeName :: (TcM Core.NamespaceTypeName)
              _justIrelationTypeName :: (TcM Core.RelationTypeName)
              _justIself :: TypeName
              _justIsortTypeName :: (TcM Core.SortTypeName)
              _self =
                  Just _justIself
              _lhsOself =
                  _self
              _justOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 5241 "src/KnotSpec/AG.hs" #-}
                   )
              _justOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 5246 "src/KnotSpec/AG.hs" #-}
                   )
              _justOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 5251 "src/KnotSpec/AG.hs" #-}
                   )
              _justOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 5256 "src/KnotSpec/AG.hs" #-}
                   )
              _justOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 5261 "src/KnotSpec/AG.hs" #-}
                   )
              _justOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 5266 "src/KnotSpec/AG.hs" #-}
                   )
              _justOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 5271 "src/KnotSpec/AG.hs" #-}
                   )
              _justOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 5276 "src/KnotSpec/AG.hs" #-}
                   )
              _justOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 5281 "src/KnotSpec/AG.hs" #-}
                   )
              ( _justIfromTn,_justInamespaceTypeName,_justIrelationTypeName,_justIself,_justIsortTypeName) =
                  just_ _justOmeEnvNameRoots _justOmeEnvTypeName _justOmeFunType _justOmeNamespaceCtor _justOmeNamespaceNameRoots _justOmeNamespaceTypeName _justOmeRelationEnv _justOmeSortNameRoots _justOmeSortTypeName
          in  ( _lhsOself)))
sem_MbTypeName_Nothing :: T_MbTypeName
sem_MbTypeName_Nothing =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOself :: MbTypeName
              _self =
                  Nothing
              _lhsOself =
                  _self
          in  ( _lhsOself)))
-- Name --------------------------------------------------------
-- cata
sem_Name :: Name ->
            T_Name
sem_Name ( x1,x2) =
    (sem_Name_Tuple x1 x2)
-- semantic domain
type T_Name = MEEnvNameRoots ->
              MEEnvTypeName ->
              MEFunType ->
              MENamespaceCtor ->
              MENamespaceNameRoots ->
              MENamespaceTypeName ->
              MERelationEnv ->
              MESortNameRoots ->
              MESortTypeName ->
              ( (TcM CoreFieldName),(TcM CoreTypeName),(TcM Core.FieldMetaBinding),(TcM Core.MetavarVar),(TcM Core.NamespaceTypeName),NameRoot,Name,(TcM Core.SubtreeVar),String)
data Inh_Name = Inh_Name {meEnvNameRoots_Inh_Name :: MEEnvNameRoots,meEnvTypeName_Inh_Name :: MEEnvTypeName,meFunType_Inh_Name :: MEFunType,meNamespaceCtor_Inh_Name :: MENamespaceCtor,meNamespaceNameRoots_Inh_Name :: MENamespaceNameRoots,meNamespaceTypeName_Inh_Name :: MENamespaceTypeName,meRelationEnv_Inh_Name :: MERelationEnv,meSortNameRoots_Inh_Name :: MESortNameRoots,meSortTypeName_Inh_Name :: MESortTypeName}
data Syn_Name = Syn_Name {coreFieldName_Syn_Name :: (TcM CoreFieldName),coreTypeName_Syn_Name :: (TcM CoreTypeName),fieldMetaBinding_Syn_Name :: (TcM Core.FieldMetaBinding),metavarName_Syn_Name :: (TcM Core.MetavarVar),namespaceTypeName_Syn_Name :: (TcM Core.NamespaceTypeName),root_Syn_Name :: NameRoot,self_Syn_Name :: Name,subtreeName_Syn_Name :: (TcM Core.SubtreeVar),suffix_Syn_Name :: String}
wrap_Name :: T_Name ->
             Inh_Name ->
             Syn_Name
wrap_Name sem (Inh_Name _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName) =
    (let ( _lhsOcoreFieldName,_lhsOcoreTypeName,_lhsOfieldMetaBinding,_lhsOmetavarName,_lhsOnamespaceTypeName,_lhsOroot,_lhsOself,_lhsOsubtreeName,_lhsOsuffix) = sem _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName
     in  (Syn_Name _lhsOcoreFieldName _lhsOcoreTypeName _lhsOfieldMetaBinding _lhsOmetavarName _lhsOnamespaceTypeName _lhsOroot _lhsOself _lhsOsubtreeName _lhsOsuffix))
sem_Name_Tuple :: NameRoot ->
                  Suffix ->
                  T_Name
sem_Name_Tuple x1_ x2_ =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOnamespaceTypeName :: (TcM Core.NamespaceTypeName)
              _lhsOmetavarName :: (TcM Core.MetavarVar)
              _lhsOsubtreeName :: (TcM Core.SubtreeVar)
              _lhsOfieldMetaBinding :: (TcM Core.FieldMetaBinding)
              _lhsOself :: Name
              _lhsOcoreFieldName :: (TcM CoreFieldName)
              _lhsOcoreTypeName :: (TcM CoreTypeName)
              _lhsOroot :: NameRoot
              _lhsOsuffix :: String
              _coreTypeName =
                  ({-# LINE 93 "src/KnotSpec/Desugaring.ag" #-}
                   let mb_ntn = Data.Map.lookup _root     _lhsImeNamespaceTypeName
                       mb_stn = Data.Map.lookup _root     _lhsImeSortTypeName
                       mb_etn = Data.Map.lookup _root     _lhsImeEnvTypeName
                   in case (mb_ntn,mb_stn,mb_etn) of
                        (Just (TN ntn), Nothing, Nothing) ->
                          return . NTN $ Core.NTN ntn
                        (Nothing , Just (TN stn), Nothing) ->
                          return . STN $ Core.STN stn
                        (Nothing , Nothing, Just (TN etn)) ->
                          return . ETN $ Core.ETN etn
                        _ -> throwError $ "Cannot find typename for nameroot: " ++ fromNR _root
                   {-# LINE 5363 "src/KnotSpec/AG.hs" #-}
                   )
              _coreFieldName =
                  ({-# LINE 105 "src/KnotSpec/Desugaring.ag" #-}
                   do
                     coreTypeName <- _coreTypeName
                     case coreTypeName of
                       NTN ntn -> return . FRN $
                                  Core.MetavarVar
                                    (Core.NR (fromNR _root    ))
                                    _suffix
                                    ntn
                       STN stn -> return . FRS $
                                  Core.SubtreeVar
                                    (Core.NR (fromNR _root    ))
                                    _suffix
                                    stn
                       ETN _ -> throwError "coreFieldName"
                   {-# LINE 5381 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOnamespaceTypeName =
                  ({-# LINE 120 "src/KnotSpec/Desugaring.ag" #-}
                   do
                     coreTypeName <- _coreTypeName
                     case coreTypeName of
                       NTN ntn -> return ntn
                       ETN _ -> throwError "namespaceTypeName"
                   {-# LINE 5390 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOmetavarName =
                  ({-# LINE 127 "src/KnotSpec/Desugaring.ag" #-}
                   do
                     mbMetavarVar <- _coreFieldName
                     case mbMetavarVar of
                       FRN metavarName -> return metavarName
                       _               -> throwError "metavarName"
                   {-# LINE 5399 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOsubtreeName =
                  ({-# LINE 133 "src/KnotSpec/Desugaring.ag" #-}
                   do
                     mbSubtreeVar <- _coreFieldName
                     case mbSubtreeVar of
                       FRS subtreeName -> return subtreeName
                       _               -> throwError "subtreeName"
                   {-# LINE 5408 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOfieldMetaBinding =
                  ({-# LINE 139 "src/KnotSpec/Desugaring.ag" #-}
                   do
                     coreFieldRef <- _coreFieldName
                     case coreFieldRef of
                       FRN metavarName -> return $ Core.FieldMetaBindingMetavar metavarName
                       FRS subtreeName -> return $ Core.FieldMetaBindingSubtree subtreeName
                   {-# LINE 5417 "src/KnotSpec/AG.hs" #-}
                   )
              _root =
                  ({-# LINE 35 "src/KnotSpec/Environment.ag" #-}
                   x1_
                   {-# LINE 5422 "src/KnotSpec/AG.hs" #-}
                   )
              _suffix =
                  ({-# LINE 36 "src/KnotSpec/Environment.ag" #-}
                   x2_
                   {-# LINE 5427 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  (x1_,x2_)
              _lhsOself =
                  _self
              _lhsOcoreFieldName =
                  ({-# LINE 81 "src/KnotSpec/Desugaring.ag" #-}
                   _coreFieldName
                   {-# LINE 5436 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOcoreTypeName =
                  ({-# LINE 80 "src/KnotSpec/Desugaring.ag" #-}
                   _coreTypeName
                   {-# LINE 5441 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOroot =
                  ({-# LINE 31 "src/KnotSpec/Environment.ag" #-}
                   _root
                   {-# LINE 5446 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOsuffix =
                  ({-# LINE 32 "src/KnotSpec/Environment.ag" #-}
                   _suffix
                   {-# LINE 5451 "src/KnotSpec/AG.hs" #-}
                   )
          in  ( _lhsOcoreFieldName,_lhsOcoreTypeName,_lhsOfieldMetaBinding,_lhsOmetavarName,_lhsOnamespaceTypeName,_lhsOroot,_lhsOself,_lhsOsubtreeName,_lhsOsuffix)))
-- NameRoots ---------------------------------------------------
-- cata
sem_NameRoots :: NameRoots ->
                 T_NameRoots
sem_NameRoots list =
    (Prelude.foldr sem_NameRoots_Cons sem_NameRoots_Nil list)
-- semantic domain
type T_NameRoots = ( NameRoots)
data Inh_NameRoots = Inh_NameRoots {}
data Syn_NameRoots = Syn_NameRoots {self_Syn_NameRoots :: NameRoots}
wrap_NameRoots :: T_NameRoots ->
                  Inh_NameRoots ->
                  Syn_NameRoots
wrap_NameRoots sem (Inh_NameRoots) =
    (let ( _lhsOself) = sem
     in  (Syn_NameRoots _lhsOself))
sem_NameRoots_Cons :: NameRoot ->
                      T_NameRoots ->
                      T_NameRoots
sem_NameRoots_Cons hd_ tl_ =
    (let _lhsOself :: NameRoots
         _tlIself :: NameRoots
         _self =
             (:) hd_ _tlIself
         _lhsOself =
             _self
         ( _tlIself) =
             tl_
     in  ( _lhsOself))
sem_NameRoots_Nil :: T_NameRoots
sem_NameRoots_Nil =
    (let _lhsOself :: NameRoots
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
-- Names -------------------------------------------------------
-- cata
sem_Names :: Names ->
             T_Names
sem_Names list =
    (Prelude.foldr sem_Names_Cons sem_Names_Nil (Prelude.map sem_Name list))
-- semantic domain
type T_Names = MEEnvNameRoots ->
               MEEnvTypeName ->
               MEFunType ->
               MENamespaceCtor ->
               MENamespaceNameRoots ->
               MENamespaceTypeName ->
               MERelationEnv ->
               MESortNameRoots ->
               MESortTypeName ->
               ( (TcM [Core.FieldMetaBinding]),Names,(TcM [Core.SubtreeVar]))
data Inh_Names = Inh_Names {meEnvNameRoots_Inh_Names :: MEEnvNameRoots,meEnvTypeName_Inh_Names :: MEEnvTypeName,meFunType_Inh_Names :: MEFunType,meNamespaceCtor_Inh_Names :: MENamespaceCtor,meNamespaceNameRoots_Inh_Names :: MENamespaceNameRoots,meNamespaceTypeName_Inh_Names :: MENamespaceTypeName,meRelationEnv_Inh_Names :: MERelationEnv,meSortNameRoots_Inh_Names :: MESortNameRoots,meSortTypeName_Inh_Names :: MESortTypeName}
data Syn_Names = Syn_Names {fieldMetaBinding_Syn_Names :: (TcM [Core.FieldMetaBinding]),self_Syn_Names :: Names,subtreeName_Syn_Names :: (TcM [Core.SubtreeVar])}
wrap_Names :: T_Names ->
              Inh_Names ->
              Syn_Names
wrap_Names sem (Inh_Names _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName) =
    (let ( _lhsOfieldMetaBinding,_lhsOself,_lhsOsubtreeName) = sem _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName
     in  (Syn_Names _lhsOfieldMetaBinding _lhsOself _lhsOsubtreeName))
sem_Names_Cons :: T_Name ->
                  T_Names ->
                  T_Names
sem_Names_Cons hd_ tl_ =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOfieldMetaBinding :: (TcM [Core.FieldMetaBinding])
              _lhsOsubtreeName :: (TcM [Core.SubtreeVar])
              _lhsOself :: Names
              _hdOmeEnvNameRoots :: MEEnvNameRoots
              _hdOmeEnvTypeName :: MEEnvTypeName
              _hdOmeFunType :: MEFunType
              _hdOmeNamespaceCtor :: MENamespaceCtor
              _hdOmeNamespaceNameRoots :: MENamespaceNameRoots
              _hdOmeNamespaceTypeName :: MENamespaceTypeName
              _hdOmeRelationEnv :: MERelationEnv
              _hdOmeSortNameRoots :: MESortNameRoots
              _hdOmeSortTypeName :: MESortTypeName
              _tlOmeEnvNameRoots :: MEEnvNameRoots
              _tlOmeEnvTypeName :: MEEnvTypeName
              _tlOmeFunType :: MEFunType
              _tlOmeNamespaceCtor :: MENamespaceCtor
              _tlOmeNamespaceNameRoots :: MENamespaceNameRoots
              _tlOmeNamespaceTypeName :: MENamespaceTypeName
              _tlOmeRelationEnv :: MERelationEnv
              _tlOmeSortNameRoots :: MESortNameRoots
              _tlOmeSortTypeName :: MESortTypeName
              _hdIcoreFieldName :: (TcM CoreFieldName)
              _hdIcoreTypeName :: (TcM CoreTypeName)
              _hdIfieldMetaBinding :: (TcM Core.FieldMetaBinding)
              _hdImetavarName :: (TcM Core.MetavarVar)
              _hdInamespaceTypeName :: (TcM Core.NamespaceTypeName)
              _hdIroot :: NameRoot
              _hdIself :: Name
              _hdIsubtreeName :: (TcM Core.SubtreeVar)
              _hdIsuffix :: String
              _tlIfieldMetaBinding :: (TcM [Core.FieldMetaBinding])
              _tlIself :: Names
              _tlIsubtreeName :: (TcM [Core.SubtreeVar])
              _lhsOfieldMetaBinding =
                  ({-# LINE 89 "src/KnotSpec/Desugaring.ag" #-}
                   (consA _hdIfieldMetaBinding _tlIfieldMetaBinding)
                   {-# LINE 5565 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOsubtreeName =
                  ({-# LINE 88 "src/KnotSpec/Desugaring.ag" #-}
                   (consA _hdIsubtreeName _tlIsubtreeName)
                   {-# LINE 5570 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _hdOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 5579 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 5584 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 5589 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 5594 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 5599 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 5604 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 5609 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 5614 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 5619 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 5624 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 5629 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 5634 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 5639 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 5644 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 5649 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 5654 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 5659 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 5664 "src/KnotSpec/AG.hs" #-}
                   )
              ( _hdIcoreFieldName,_hdIcoreTypeName,_hdIfieldMetaBinding,_hdImetavarName,_hdInamespaceTypeName,_hdIroot,_hdIself,_hdIsubtreeName,_hdIsuffix) =
                  hd_ _hdOmeEnvNameRoots _hdOmeEnvTypeName _hdOmeFunType _hdOmeNamespaceCtor _hdOmeNamespaceNameRoots _hdOmeNamespaceTypeName _hdOmeRelationEnv _hdOmeSortNameRoots _hdOmeSortTypeName
              ( _tlIfieldMetaBinding,_tlIself,_tlIsubtreeName) =
                  tl_ _tlOmeEnvNameRoots _tlOmeEnvTypeName _tlOmeFunType _tlOmeNamespaceCtor _tlOmeNamespaceNameRoots _tlOmeNamespaceTypeName _tlOmeRelationEnv _tlOmeSortNameRoots _tlOmeSortTypeName
          in  ( _lhsOfieldMetaBinding,_lhsOself,_lhsOsubtreeName)))
sem_Names_Nil :: T_Names
sem_Names_Nil =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOfieldMetaBinding :: (TcM [Core.FieldMetaBinding])
              _lhsOsubtreeName :: (TcM [Core.SubtreeVar])
              _lhsOself :: Names
              _lhsOfieldMetaBinding =
                  ({-# LINE 89 "src/KnotSpec/Desugaring.ag" #-}
                   memptyA
                   {-# LINE 5688 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOsubtreeName =
                  ({-# LINE 88 "src/KnotSpec/Desugaring.ag" #-}
                   memptyA
                   {-# LINE 5693 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  []
              _lhsOself =
                  _self
          in  ( _lhsOfieldMetaBinding,_lhsOself,_lhsOsubtreeName)))
-- NamespaceDecl -----------------------------------------------
-- cata
sem_NamespaceDecl :: NamespaceDecl ->
                     T_NamespaceDecl
sem_NamespaceDecl (NamespaceDecl _nsdTypeName _nsdNameRoots _nsdSort _nsdDirectives) =
    (sem_NamespaceDecl_NamespaceDecl (sem_TypeName _nsdTypeName) (sem_NameRoots _nsdNameRoots) (sem_TypeName _nsdSort) (sem_NamespaceDirectives _nsdDirectives))
-- semantic domain
type T_NamespaceDecl = MEEnvNameRoots ->
                       MEEnvTypeName ->
                       MEFunType ->
                       MENamespaceCtor ->
                       MENamespaceNameRoots ->
                       MENamespaceTypeName ->
                       MERelationEnv ->
                       MESortNameRoots ->
                       MESortTypeName ->
                       ( (TcM Core.NamespaceDecl),NamespaceDecl,MENamespaceNameRoots)
data Inh_NamespaceDecl = Inh_NamespaceDecl {meEnvNameRoots_Inh_NamespaceDecl :: MEEnvNameRoots,meEnvTypeName_Inh_NamespaceDecl :: MEEnvTypeName,meFunType_Inh_NamespaceDecl :: MEFunType,meNamespaceCtor_Inh_NamespaceDecl :: MENamespaceCtor,meNamespaceNameRoots_Inh_NamespaceDecl :: MENamespaceNameRoots,meNamespaceTypeName_Inh_NamespaceDecl :: MENamespaceTypeName,meRelationEnv_Inh_NamespaceDecl :: MERelationEnv,meSortNameRoots_Inh_NamespaceDecl :: MESortNameRoots,meSortTypeName_Inh_NamespaceDecl :: MESortTypeName}
data Syn_NamespaceDecl = Syn_NamespaceDecl {desugared_Syn_NamespaceDecl :: (TcM Core.NamespaceDecl),self_Syn_NamespaceDecl :: NamespaceDecl,smeNamespaceNameRoots_Syn_NamespaceDecl :: MENamespaceNameRoots}
wrap_NamespaceDecl :: T_NamespaceDecl ->
                      Inh_NamespaceDecl ->
                      Syn_NamespaceDecl
wrap_NamespaceDecl sem (Inh_NamespaceDecl _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName) =
    (let ( _lhsOdesugared,_lhsOself,_lhsOsmeNamespaceNameRoots) = sem _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName
     in  (Syn_NamespaceDecl _lhsOdesugared _lhsOself _lhsOsmeNamespaceNameRoots))
sem_NamespaceDecl_NamespaceDecl :: T_TypeName ->
                                   T_NameRoots ->
                                   T_TypeName ->
                                   T_NamespaceDirectives ->
                                   T_NamespaceDecl
sem_NamespaceDecl_NamespaceDecl nsdTypeName_ nsdNameRoots_ nsdSort_ nsdDirectives_ =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOsmeNamespaceNameRoots :: MENamespaceNameRoots
              _lhsOself :: NamespaceDecl
              _lhsOdesugared :: (TcM Core.NamespaceDecl)
              _nsdTypeNameOmeEnvNameRoots :: MEEnvNameRoots
              _nsdTypeNameOmeEnvTypeName :: MEEnvTypeName
              _nsdTypeNameOmeFunType :: MEFunType
              _nsdTypeNameOmeNamespaceCtor :: MENamespaceCtor
              _nsdTypeNameOmeNamespaceNameRoots :: MENamespaceNameRoots
              _nsdTypeNameOmeNamespaceTypeName :: MENamespaceTypeName
              _nsdTypeNameOmeRelationEnv :: MERelationEnv
              _nsdTypeNameOmeSortNameRoots :: MESortNameRoots
              _nsdTypeNameOmeSortTypeName :: MESortTypeName
              _nsdSortOmeEnvNameRoots :: MEEnvNameRoots
              _nsdSortOmeEnvTypeName :: MEEnvTypeName
              _nsdSortOmeFunType :: MEFunType
              _nsdSortOmeNamespaceCtor :: MENamespaceCtor
              _nsdSortOmeNamespaceNameRoots :: MENamespaceNameRoots
              _nsdSortOmeNamespaceTypeName :: MENamespaceTypeName
              _nsdSortOmeRelationEnv :: MERelationEnv
              _nsdSortOmeSortNameRoots :: MESortNameRoots
              _nsdSortOmeSortTypeName :: MESortTypeName
              _nsdTypeNameIfromTn :: String
              _nsdTypeNameInamespaceTypeName :: (TcM Core.NamespaceTypeName)
              _nsdTypeNameIrelationTypeName :: (TcM Core.RelationTypeName)
              _nsdTypeNameIself :: TypeName
              _nsdTypeNameIsortTypeName :: (TcM Core.SortTypeName)
              _nsdNameRootsIself :: NameRoots
              _nsdSortIfromTn :: String
              _nsdSortInamespaceTypeName :: (TcM Core.NamespaceTypeName)
              _nsdSortIrelationTypeName :: (TcM Core.RelationTypeName)
              _nsdSortIself :: TypeName
              _nsdSortIsortTypeName :: (TcM Core.SortTypeName)
              _nsdDirectivesIself :: NamespaceDirectives
              _desugared =
                  ({-# LINE 212 "src/KnotSpec/Desugaring.ag" #-}
                   do
                     (variableSort,variableCtor) <-
                       maybe
                         (throwError $
                            "No variable constructor for namespace " ++ _nsdTypeNameIfromTn)
                         return
                         (Data.Map.lookup
                            _typeName
                            _lhsImeNamespaceCtor)
                     shiftName <-
                       case [s | NamespaceShift s <- _nsdDirectivesIself] of
                         []  -> return $ "shift_" ++ _nsdTypeNameIfromTn ++ "_"
                         [s] -> return s
                         ss  -> throwError $ "more than one shift root defined: " ++
                                  intercalate ", " ss
                     substName <-
                       case [s | NamespaceSubst s <- _nsdDirectivesIself] of
                         []  -> return $ "subst_" ++ _nsdTypeNameIfromTn ++ "_"
                         [s] -> return s
                         ss  -> throwError $ "more than one subst root defined: " ++
                                  intercalate ", " ss
                     return $ Core.NamespaceDecl
                                (Core.NTN _nsdTypeNameIfromTn)
                                (map (Core.NR . fromNR) _nsdNameRootsIself)
                                (Core.STN _nsdSortIfromTn)
                                (Core.CNS variableCtor (Core.STN _nsdSortIfromTn))
                                shiftName
                                substName
                   {-# LINE 5803 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOsmeNamespaceNameRoots =
                  ({-# LINE 74 "src/KnotSpec/Environment.ag" #-}
                   Data.Map.singleton _nsdTypeNameIself _nsdNameRootsIself
                   {-# LINE 5808 "src/KnotSpec/AG.hs" #-}
                   )
              _typeName =
                  ({-# LINE 75 "src/KnotSpec/Environment.ag" #-}
                   _nsdTypeNameIself
                   {-# LINE 5813 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  NamespaceDecl _nsdTypeNameIself _nsdNameRootsIself _nsdSortIself _nsdDirectivesIself
              _lhsOself =
                  _self
              _lhsOdesugared =
                  ({-# LINE 170 "src/KnotSpec/Desugaring.ag" #-}
                   _desugared
                   {-# LINE 5822 "src/KnotSpec/AG.hs" #-}
                   )
              _nsdTypeNameOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 5827 "src/KnotSpec/AG.hs" #-}
                   )
              _nsdTypeNameOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 5832 "src/KnotSpec/AG.hs" #-}
                   )
              _nsdTypeNameOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 5837 "src/KnotSpec/AG.hs" #-}
                   )
              _nsdTypeNameOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 5842 "src/KnotSpec/AG.hs" #-}
                   )
              _nsdTypeNameOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 5847 "src/KnotSpec/AG.hs" #-}
                   )
              _nsdTypeNameOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 5852 "src/KnotSpec/AG.hs" #-}
                   )
              _nsdTypeNameOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 5857 "src/KnotSpec/AG.hs" #-}
                   )
              _nsdTypeNameOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 5862 "src/KnotSpec/AG.hs" #-}
                   )
              _nsdTypeNameOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 5867 "src/KnotSpec/AG.hs" #-}
                   )
              _nsdSortOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 5872 "src/KnotSpec/AG.hs" #-}
                   )
              _nsdSortOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 5877 "src/KnotSpec/AG.hs" #-}
                   )
              _nsdSortOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 5882 "src/KnotSpec/AG.hs" #-}
                   )
              _nsdSortOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 5887 "src/KnotSpec/AG.hs" #-}
                   )
              _nsdSortOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 5892 "src/KnotSpec/AG.hs" #-}
                   )
              _nsdSortOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 5897 "src/KnotSpec/AG.hs" #-}
                   )
              _nsdSortOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 5902 "src/KnotSpec/AG.hs" #-}
                   )
              _nsdSortOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 5907 "src/KnotSpec/AG.hs" #-}
                   )
              _nsdSortOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 5912 "src/KnotSpec/AG.hs" #-}
                   )
              ( _nsdTypeNameIfromTn,_nsdTypeNameInamespaceTypeName,_nsdTypeNameIrelationTypeName,_nsdTypeNameIself,_nsdTypeNameIsortTypeName) =
                  nsdTypeName_ _nsdTypeNameOmeEnvNameRoots _nsdTypeNameOmeEnvTypeName _nsdTypeNameOmeFunType _nsdTypeNameOmeNamespaceCtor _nsdTypeNameOmeNamespaceNameRoots _nsdTypeNameOmeNamespaceTypeName _nsdTypeNameOmeRelationEnv _nsdTypeNameOmeSortNameRoots _nsdTypeNameOmeSortTypeName
              ( _nsdNameRootsIself) =
                  nsdNameRoots_
              ( _nsdSortIfromTn,_nsdSortInamespaceTypeName,_nsdSortIrelationTypeName,_nsdSortIself,_nsdSortIsortTypeName) =
                  nsdSort_ _nsdSortOmeEnvNameRoots _nsdSortOmeEnvTypeName _nsdSortOmeFunType _nsdSortOmeNamespaceCtor _nsdSortOmeNamespaceNameRoots _nsdSortOmeNamespaceTypeName _nsdSortOmeRelationEnv _nsdSortOmeSortNameRoots _nsdSortOmeSortTypeName
              ( _nsdDirectivesIself) =
                  nsdDirectives_
          in  ( _lhsOdesugared,_lhsOself,_lhsOsmeNamespaceNameRoots)))
-- NamespaceDecls ----------------------------------------------
-- cata
sem_NamespaceDecls :: NamespaceDecls ->
                      T_NamespaceDecls
sem_NamespaceDecls list =
    (Prelude.foldr sem_NamespaceDecls_Cons sem_NamespaceDecls_Nil (Prelude.map sem_NamespaceDecl list))
-- semantic domain
type T_NamespaceDecls = MEEnvNameRoots ->
                        MEEnvTypeName ->
                        MEFunType ->
                        MENamespaceCtor ->
                        MENamespaceNameRoots ->
                        MENamespaceTypeName ->
                        MERelationEnv ->
                        MESortNameRoots ->
                        MESortTypeName ->
                        ( (TcM [Core.NamespaceDecl]),NamespaceDecls,MENamespaceNameRoots)
data Inh_NamespaceDecls = Inh_NamespaceDecls {meEnvNameRoots_Inh_NamespaceDecls :: MEEnvNameRoots,meEnvTypeName_Inh_NamespaceDecls :: MEEnvTypeName,meFunType_Inh_NamespaceDecls :: MEFunType,meNamespaceCtor_Inh_NamespaceDecls :: MENamespaceCtor,meNamespaceNameRoots_Inh_NamespaceDecls :: MENamespaceNameRoots,meNamespaceTypeName_Inh_NamespaceDecls :: MENamespaceTypeName,meRelationEnv_Inh_NamespaceDecls :: MERelationEnv,meSortNameRoots_Inh_NamespaceDecls :: MESortNameRoots,meSortTypeName_Inh_NamespaceDecls :: MESortTypeName}
data Syn_NamespaceDecls = Syn_NamespaceDecls {desugared_Syn_NamespaceDecls :: (TcM [Core.NamespaceDecl]),self_Syn_NamespaceDecls :: NamespaceDecls,smeNamespaceNameRoots_Syn_NamespaceDecls :: MENamespaceNameRoots}
wrap_NamespaceDecls :: T_NamespaceDecls ->
                       Inh_NamespaceDecls ->
                       Syn_NamespaceDecls
wrap_NamespaceDecls sem (Inh_NamespaceDecls _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName) =
    (let ( _lhsOdesugared,_lhsOself,_lhsOsmeNamespaceNameRoots) = sem _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName
     in  (Syn_NamespaceDecls _lhsOdesugared _lhsOself _lhsOsmeNamespaceNameRoots))
sem_NamespaceDecls_Cons :: T_NamespaceDecl ->
                           T_NamespaceDecls ->
                           T_NamespaceDecls
sem_NamespaceDecls_Cons hd_ tl_ =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOdesugared :: (TcM [Core.NamespaceDecl])
              _lhsOsmeNamespaceNameRoots :: MENamespaceNameRoots
              _lhsOself :: NamespaceDecls
              _hdOmeEnvNameRoots :: MEEnvNameRoots
              _hdOmeEnvTypeName :: MEEnvTypeName
              _hdOmeFunType :: MEFunType
              _hdOmeNamespaceCtor :: MENamespaceCtor
              _hdOmeNamespaceNameRoots :: MENamespaceNameRoots
              _hdOmeNamespaceTypeName :: MENamespaceTypeName
              _hdOmeRelationEnv :: MERelationEnv
              _hdOmeSortNameRoots :: MESortNameRoots
              _hdOmeSortTypeName :: MESortTypeName
              _tlOmeEnvNameRoots :: MEEnvNameRoots
              _tlOmeEnvTypeName :: MEEnvTypeName
              _tlOmeFunType :: MEFunType
              _tlOmeNamespaceCtor :: MENamespaceCtor
              _tlOmeNamespaceNameRoots :: MENamespaceNameRoots
              _tlOmeNamespaceTypeName :: MENamespaceTypeName
              _tlOmeRelationEnv :: MERelationEnv
              _tlOmeSortNameRoots :: MESortNameRoots
              _tlOmeSortTypeName :: MESortTypeName
              _hdIdesugared :: (TcM Core.NamespaceDecl)
              _hdIself :: NamespaceDecl
              _hdIsmeNamespaceNameRoots :: MENamespaceNameRoots
              _tlIdesugared :: (TcM [Core.NamespaceDecl])
              _tlIself :: NamespaceDecls
              _tlIsmeNamespaceNameRoots :: MENamespaceNameRoots
              _lhsOdesugared =
                  ({-# LINE 169 "src/KnotSpec/Desugaring.ag" #-}
                   (consA _hdIdesugared _tlIdesugared)
                   {-# LINE 5991 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOsmeNamespaceNameRoots =
                  ({-# LINE 68 "src/KnotSpec/Environment.ag" #-}
                   (Data.Map.unionWith (error "smeNamespaceNameRoots union") _hdIsmeNamespaceNameRoots _tlIsmeNamespaceNameRoots)
                   {-# LINE 5996 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _hdOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 6005 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 6010 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 6015 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 6020 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 6025 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 6030 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 6035 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 6040 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 6045 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 6050 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 6055 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 6060 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 6065 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 6070 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 6075 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 6080 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 6085 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 6090 "src/KnotSpec/AG.hs" #-}
                   )
              ( _hdIdesugared,_hdIself,_hdIsmeNamespaceNameRoots) =
                  hd_ _hdOmeEnvNameRoots _hdOmeEnvTypeName _hdOmeFunType _hdOmeNamespaceCtor _hdOmeNamespaceNameRoots _hdOmeNamespaceTypeName _hdOmeRelationEnv _hdOmeSortNameRoots _hdOmeSortTypeName
              ( _tlIdesugared,_tlIself,_tlIsmeNamespaceNameRoots) =
                  tl_ _tlOmeEnvNameRoots _tlOmeEnvTypeName _tlOmeFunType _tlOmeNamespaceCtor _tlOmeNamespaceNameRoots _tlOmeNamespaceTypeName _tlOmeRelationEnv _tlOmeSortNameRoots _tlOmeSortTypeName
          in  ( _lhsOdesugared,_lhsOself,_lhsOsmeNamespaceNameRoots)))
sem_NamespaceDecls_Nil :: T_NamespaceDecls
sem_NamespaceDecls_Nil =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOdesugared :: (TcM [Core.NamespaceDecl])
              _lhsOsmeNamespaceNameRoots :: MENamespaceNameRoots
              _lhsOself :: NamespaceDecls
              _lhsOdesugared =
                  ({-# LINE 169 "src/KnotSpec/Desugaring.ag" #-}
                   memptyA
                   {-# LINE 6114 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOsmeNamespaceNameRoots =
                  ({-# LINE 68 "src/KnotSpec/Environment.ag" #-}
                   mempty
                   {-# LINE 6119 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  []
              _lhsOself =
                  _self
          in  ( _lhsOdesugared,_lhsOself,_lhsOsmeNamespaceNameRoots)))
-- NamespaceDirective ------------------------------------------
-- cata
sem_NamespaceDirective :: NamespaceDirective ->
                          T_NamespaceDirective
sem_NamespaceDirective (NamespaceShift _nsdShiftName) =
    (sem_NamespaceDirective_NamespaceShift _nsdShiftName)
sem_NamespaceDirective (NamespaceSubst _nsdSubstName) =
    (sem_NamespaceDirective_NamespaceSubst _nsdSubstName)
sem_NamespaceDirective (NamespaceWeaken _nsdWeakenName) =
    (sem_NamespaceDirective_NamespaceWeaken _nsdWeakenName)
sem_NamespaceDirective (NamespaceCutoff _nsdCutoffName) =
    (sem_NamespaceDirective_NamespaceCutoff _nsdCutoffName)
-- semantic domain
type T_NamespaceDirective = ( NamespaceDirective)
data Inh_NamespaceDirective = Inh_NamespaceDirective {}
data Syn_NamespaceDirective = Syn_NamespaceDirective {self_Syn_NamespaceDirective :: NamespaceDirective}
wrap_NamespaceDirective :: T_NamespaceDirective ->
                           Inh_NamespaceDirective ->
                           Syn_NamespaceDirective
wrap_NamespaceDirective sem (Inh_NamespaceDirective) =
    (let ( _lhsOself) = sem
     in  (Syn_NamespaceDirective _lhsOself))
sem_NamespaceDirective_NamespaceShift :: String ->
                                         T_NamespaceDirective
sem_NamespaceDirective_NamespaceShift nsdShiftName_ =
    (let _lhsOself :: NamespaceDirective
         _self =
             NamespaceShift nsdShiftName_
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_NamespaceDirective_NamespaceSubst :: String ->
                                         T_NamespaceDirective
sem_NamespaceDirective_NamespaceSubst nsdSubstName_ =
    (let _lhsOself :: NamespaceDirective
         _self =
             NamespaceSubst nsdSubstName_
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_NamespaceDirective_NamespaceWeaken :: String ->
                                          T_NamespaceDirective
sem_NamespaceDirective_NamespaceWeaken nsdWeakenName_ =
    (let _lhsOself :: NamespaceDirective
         _self =
             NamespaceWeaken nsdWeakenName_
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_NamespaceDirective_NamespaceCutoff :: String ->
                                          T_NamespaceDirective
sem_NamespaceDirective_NamespaceCutoff nsdCutoffName_ =
    (let _lhsOself :: NamespaceDirective
         _self =
             NamespaceCutoff nsdCutoffName_
         _lhsOself =
             _self
     in  ( _lhsOself))
-- NamespaceDirectives -----------------------------------------
-- cata
sem_NamespaceDirectives :: NamespaceDirectives ->
                           T_NamespaceDirectives
sem_NamespaceDirectives list =
    (Prelude.foldr sem_NamespaceDirectives_Cons sem_NamespaceDirectives_Nil (Prelude.map sem_NamespaceDirective list))
-- semantic domain
type T_NamespaceDirectives = ( NamespaceDirectives)
data Inh_NamespaceDirectives = Inh_NamespaceDirectives {}
data Syn_NamespaceDirectives = Syn_NamespaceDirectives {self_Syn_NamespaceDirectives :: NamespaceDirectives}
wrap_NamespaceDirectives :: T_NamespaceDirectives ->
                            Inh_NamespaceDirectives ->
                            Syn_NamespaceDirectives
wrap_NamespaceDirectives sem (Inh_NamespaceDirectives) =
    (let ( _lhsOself) = sem
     in  (Syn_NamespaceDirectives _lhsOself))
sem_NamespaceDirectives_Cons :: T_NamespaceDirective ->
                                T_NamespaceDirectives ->
                                T_NamespaceDirectives
sem_NamespaceDirectives_Cons hd_ tl_ =
    (let _lhsOself :: NamespaceDirectives
         _hdIself :: NamespaceDirective
         _tlIself :: NamespaceDirectives
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             hd_
         ( _tlIself) =
             tl_
     in  ( _lhsOself))
sem_NamespaceDirectives_Nil :: T_NamespaceDirectives
sem_NamespaceDirectives_Nil =
    (let _lhsOself :: NamespaceDirectives
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
-- RelationDecl ------------------------------------------------
-- cata
sem_RelationDecl :: RelationDecl ->
                    T_RelationDecl
sem_RelationDecl (RelationDecl _relEnv _relTypeName _relIndices _relRules) =
    (sem_RelationDecl_RelationDecl (sem_MbTypeName _relEnv) (sem_TypeName _relTypeName) (sem_TypeNames _relIndices) (sem_Rules _relRules))
-- semantic domain
type T_RelationDecl = MEEnvNameRoots ->
                      MEEnvTypeName ->
                      MEFunType ->
                      MENamespaceCtor ->
                      MENamespaceNameRoots ->
                      MENamespaceTypeName ->
                      MERelationEnv ->
                      MESortNameRoots ->
                      MESortTypeName ->
                      ( (TcM Core.RelationDecl),RelationDecl,MERelationEnv)
data Inh_RelationDecl = Inh_RelationDecl {meEnvNameRoots_Inh_RelationDecl :: MEEnvNameRoots,meEnvTypeName_Inh_RelationDecl :: MEEnvTypeName,meFunType_Inh_RelationDecl :: MEFunType,meNamespaceCtor_Inh_RelationDecl :: MENamespaceCtor,meNamespaceNameRoots_Inh_RelationDecl :: MENamespaceNameRoots,meNamespaceTypeName_Inh_RelationDecl :: MENamespaceTypeName,meRelationEnv_Inh_RelationDecl :: MERelationEnv,meSortNameRoots_Inh_RelationDecl :: MESortNameRoots,meSortTypeName_Inh_RelationDecl :: MESortTypeName}
data Syn_RelationDecl = Syn_RelationDecl {desugared_Syn_RelationDecl :: (TcM Core.RelationDecl),self_Syn_RelationDecl :: RelationDecl,smeRelationEnv_Syn_RelationDecl :: MERelationEnv}
wrap_RelationDecl :: T_RelationDecl ->
                     Inh_RelationDecl ->
                     Syn_RelationDecl
wrap_RelationDecl sem (Inh_RelationDecl _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName) =
    (let ( _lhsOdesugared,_lhsOself,_lhsOsmeRelationEnv) = sem _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName
     in  (Syn_RelationDecl _lhsOdesugared _lhsOself _lhsOsmeRelationEnv))
sem_RelationDecl_RelationDecl :: T_MbTypeName ->
                                 T_TypeName ->
                                 T_TypeNames ->
                                 T_Rules ->
                                 T_RelationDecl
sem_RelationDecl_RelationDecl relEnv_ relTypeName_ relIndices_ relRules_ =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOsmeRelationEnv :: MERelationEnv
              _lhsOself :: RelationDecl
              _lhsOdesugared :: (TcM Core.RelationDecl)
              _relEnvOmeEnvNameRoots :: MEEnvNameRoots
              _relEnvOmeEnvTypeName :: MEEnvTypeName
              _relEnvOmeFunType :: MEFunType
              _relEnvOmeNamespaceCtor :: MENamespaceCtor
              _relEnvOmeNamespaceNameRoots :: MENamespaceNameRoots
              _relEnvOmeNamespaceTypeName :: MENamespaceTypeName
              _relEnvOmeRelationEnv :: MERelationEnv
              _relEnvOmeSortNameRoots :: MESortNameRoots
              _relEnvOmeSortTypeName :: MESortTypeName
              _relTypeNameOmeEnvNameRoots :: MEEnvNameRoots
              _relTypeNameOmeEnvTypeName :: MEEnvTypeName
              _relTypeNameOmeFunType :: MEFunType
              _relTypeNameOmeNamespaceCtor :: MENamespaceCtor
              _relTypeNameOmeNamespaceNameRoots :: MENamespaceNameRoots
              _relTypeNameOmeNamespaceTypeName :: MENamespaceTypeName
              _relTypeNameOmeRelationEnv :: MERelationEnv
              _relTypeNameOmeSortNameRoots :: MESortNameRoots
              _relTypeNameOmeSortTypeName :: MESortTypeName
              _relIndicesOmeEnvNameRoots :: MEEnvNameRoots
              _relIndicesOmeEnvTypeName :: MEEnvTypeName
              _relIndicesOmeFunType :: MEFunType
              _relIndicesOmeNamespaceCtor :: MENamespaceCtor
              _relIndicesOmeNamespaceNameRoots :: MENamespaceNameRoots
              _relIndicesOmeNamespaceTypeName :: MENamespaceTypeName
              _relIndicesOmeRelationEnv :: MERelationEnv
              _relIndicesOmeSortNameRoots :: MESortNameRoots
              _relIndicesOmeSortTypeName :: MESortTypeName
              _relRulesOmeEnvNameRoots :: MEEnvNameRoots
              _relRulesOmeEnvTypeName :: MEEnvTypeName
              _relRulesOmeFunType :: MEFunType
              _relRulesOmeNamespaceCtor :: MENamespaceCtor
              _relRulesOmeNamespaceNameRoots :: MENamespaceNameRoots
              _relRulesOmeNamespaceTypeName :: MENamespaceTypeName
              _relRulesOmeRelationEnv :: MERelationEnv
              _relRulesOmeSortNameRoots :: MESortNameRoots
              _relRulesOmeSortTypeName :: MESortTypeName
              _relEnvIself :: MbTypeName
              _relTypeNameIfromTn :: String
              _relTypeNameInamespaceTypeName :: (TcM Core.NamespaceTypeName)
              _relTypeNameIrelationTypeName :: (TcM Core.RelationTypeName)
              _relTypeNameIself :: TypeName
              _relTypeNameIsortTypeName :: (TcM Core.SortTypeName)
              _relIndicesInamespaceTypeName :: (TcM [Core.NamespaceTypeName])
              _relIndicesIself :: TypeNames
              _relRulesIdesugared :: (TcM [Core.Rule])
              _relRulesIself :: Rules
              _coreMbEnvName =
                  ({-# LINE 353 "src/KnotSpec/Desugaring.ag" #-}
                   do
                     tn@(TN etn) <- _relEnvIself
                     nrs <- Data.Map.lookup tn _lhsImeEnvNameRoots
                     return (Core.EnvVar (Core.NR . fromNR $ head nrs) "" (Core.ETN etn))
                   {-# LINE 6319 "src/KnotSpec/AG.hs" #-}
                   )
              _coreIndices =
                  ({-# LINE 358 "src/KnotSpec/Desugaring.ag" #-}
                   map (Core.STN . fromTN) _relIndicesIself
                   {-# LINE 6324 "src/KnotSpec/AG.hs" #-}
                   )
              _desugared =
                  ({-# LINE 359 "src/KnotSpec/Desugaring.ag" #-}
                   Core.RelationDecl
                     <$> pure _coreMbEnvName
                     <*> _relTypeNameIrelationTypeName
                     <*> pure _coreIndices
                     <*> _relRulesIdesugared
                   {-# LINE 6333 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOsmeRelationEnv =
                  ({-# LINE 239 "src/KnotSpec/Environment.ag" #-}
                   case _relEnvIself of
                     Just etn -> Data.Map.singleton _relTypeNameIself etn
                     Nothing  -> mempty
                   {-# LINE 6340 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  RelationDecl _relEnvIself _relTypeNameIself _relIndicesIself _relRulesIself
              _lhsOself =
                  _self
              _lhsOdesugared =
                  ({-# LINE 349 "src/KnotSpec/Desugaring.ag" #-}
                   _desugared
                   {-# LINE 6349 "src/KnotSpec/AG.hs" #-}
                   )
              _relEnvOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 6354 "src/KnotSpec/AG.hs" #-}
                   )
              _relEnvOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 6359 "src/KnotSpec/AG.hs" #-}
                   )
              _relEnvOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 6364 "src/KnotSpec/AG.hs" #-}
                   )
              _relEnvOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 6369 "src/KnotSpec/AG.hs" #-}
                   )
              _relEnvOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 6374 "src/KnotSpec/AG.hs" #-}
                   )
              _relEnvOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 6379 "src/KnotSpec/AG.hs" #-}
                   )
              _relEnvOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 6384 "src/KnotSpec/AG.hs" #-}
                   )
              _relEnvOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 6389 "src/KnotSpec/AG.hs" #-}
                   )
              _relEnvOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 6394 "src/KnotSpec/AG.hs" #-}
                   )
              _relTypeNameOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 6399 "src/KnotSpec/AG.hs" #-}
                   )
              _relTypeNameOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 6404 "src/KnotSpec/AG.hs" #-}
                   )
              _relTypeNameOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 6409 "src/KnotSpec/AG.hs" #-}
                   )
              _relTypeNameOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 6414 "src/KnotSpec/AG.hs" #-}
                   )
              _relTypeNameOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 6419 "src/KnotSpec/AG.hs" #-}
                   )
              _relTypeNameOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 6424 "src/KnotSpec/AG.hs" #-}
                   )
              _relTypeNameOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 6429 "src/KnotSpec/AG.hs" #-}
                   )
              _relTypeNameOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 6434 "src/KnotSpec/AG.hs" #-}
                   )
              _relTypeNameOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 6439 "src/KnotSpec/AG.hs" #-}
                   )
              _relIndicesOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 6444 "src/KnotSpec/AG.hs" #-}
                   )
              _relIndicesOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 6449 "src/KnotSpec/AG.hs" #-}
                   )
              _relIndicesOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 6454 "src/KnotSpec/AG.hs" #-}
                   )
              _relIndicesOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 6459 "src/KnotSpec/AG.hs" #-}
                   )
              _relIndicesOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 6464 "src/KnotSpec/AG.hs" #-}
                   )
              _relIndicesOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 6469 "src/KnotSpec/AG.hs" #-}
                   )
              _relIndicesOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 6474 "src/KnotSpec/AG.hs" #-}
                   )
              _relIndicesOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 6479 "src/KnotSpec/AG.hs" #-}
                   )
              _relIndicesOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 6484 "src/KnotSpec/AG.hs" #-}
                   )
              _relRulesOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 6489 "src/KnotSpec/AG.hs" #-}
                   )
              _relRulesOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 6494 "src/KnotSpec/AG.hs" #-}
                   )
              _relRulesOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 6499 "src/KnotSpec/AG.hs" #-}
                   )
              _relRulesOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 6504 "src/KnotSpec/AG.hs" #-}
                   )
              _relRulesOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 6509 "src/KnotSpec/AG.hs" #-}
                   )
              _relRulesOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 6514 "src/KnotSpec/AG.hs" #-}
                   )
              _relRulesOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 6519 "src/KnotSpec/AG.hs" #-}
                   )
              _relRulesOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 6524 "src/KnotSpec/AG.hs" #-}
                   )
              _relRulesOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 6529 "src/KnotSpec/AG.hs" #-}
                   )
              ( _relEnvIself) =
                  relEnv_ _relEnvOmeEnvNameRoots _relEnvOmeEnvTypeName _relEnvOmeFunType _relEnvOmeNamespaceCtor _relEnvOmeNamespaceNameRoots _relEnvOmeNamespaceTypeName _relEnvOmeRelationEnv _relEnvOmeSortNameRoots _relEnvOmeSortTypeName
              ( _relTypeNameIfromTn,_relTypeNameInamespaceTypeName,_relTypeNameIrelationTypeName,_relTypeNameIself,_relTypeNameIsortTypeName) =
                  relTypeName_ _relTypeNameOmeEnvNameRoots _relTypeNameOmeEnvTypeName _relTypeNameOmeFunType _relTypeNameOmeNamespaceCtor _relTypeNameOmeNamespaceNameRoots _relTypeNameOmeNamespaceTypeName _relTypeNameOmeRelationEnv _relTypeNameOmeSortNameRoots _relTypeNameOmeSortTypeName
              ( _relIndicesInamespaceTypeName,_relIndicesIself) =
                  relIndices_ _relIndicesOmeEnvNameRoots _relIndicesOmeEnvTypeName _relIndicesOmeFunType _relIndicesOmeNamespaceCtor _relIndicesOmeNamespaceNameRoots _relIndicesOmeNamespaceTypeName _relIndicesOmeRelationEnv _relIndicesOmeSortNameRoots _relIndicesOmeSortTypeName
              ( _relRulesIdesugared,_relRulesIself) =
                  relRules_ _relRulesOmeEnvNameRoots _relRulesOmeEnvTypeName _relRulesOmeFunType _relRulesOmeNamespaceCtor _relRulesOmeNamespaceNameRoots _relRulesOmeNamespaceTypeName _relRulesOmeRelationEnv _relRulesOmeSortNameRoots _relRulesOmeSortTypeName
          in  ( _lhsOdesugared,_lhsOself,_lhsOsmeRelationEnv)))
-- RelationDecls -----------------------------------------------
-- cata
sem_RelationDecls :: RelationDecls ->
                     T_RelationDecls
sem_RelationDecls list =
    (Prelude.foldr sem_RelationDecls_Cons sem_RelationDecls_Nil (Prelude.map sem_RelationDecl list))
-- semantic domain
type T_RelationDecls = MEEnvNameRoots ->
                       MEEnvTypeName ->
                       MEFunType ->
                       MENamespaceCtor ->
                       MENamespaceNameRoots ->
                       MENamespaceTypeName ->
                       MERelationEnv ->
                       MESortNameRoots ->
                       MESortTypeName ->
                       ( (TcM [Core.RelationDecl]),RelationDecls,MERelationEnv)
data Inh_RelationDecls = Inh_RelationDecls {meEnvNameRoots_Inh_RelationDecls :: MEEnvNameRoots,meEnvTypeName_Inh_RelationDecls :: MEEnvTypeName,meFunType_Inh_RelationDecls :: MEFunType,meNamespaceCtor_Inh_RelationDecls :: MENamespaceCtor,meNamespaceNameRoots_Inh_RelationDecls :: MENamespaceNameRoots,meNamespaceTypeName_Inh_RelationDecls :: MENamespaceTypeName,meRelationEnv_Inh_RelationDecls :: MERelationEnv,meSortNameRoots_Inh_RelationDecls :: MESortNameRoots,meSortTypeName_Inh_RelationDecls :: MESortTypeName}
data Syn_RelationDecls = Syn_RelationDecls {desugared_Syn_RelationDecls :: (TcM [Core.RelationDecl]),self_Syn_RelationDecls :: RelationDecls,smeRelationEnv_Syn_RelationDecls :: MERelationEnv}
wrap_RelationDecls :: T_RelationDecls ->
                      Inh_RelationDecls ->
                      Syn_RelationDecls
wrap_RelationDecls sem (Inh_RelationDecls _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName) =
    (let ( _lhsOdesugared,_lhsOself,_lhsOsmeRelationEnv) = sem _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName
     in  (Syn_RelationDecls _lhsOdesugared _lhsOself _lhsOsmeRelationEnv))
sem_RelationDecls_Cons :: T_RelationDecl ->
                          T_RelationDecls ->
                          T_RelationDecls
sem_RelationDecls_Cons hd_ tl_ =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOdesugared :: (TcM [Core.RelationDecl])
              _lhsOsmeRelationEnv :: MERelationEnv
              _lhsOself :: RelationDecls
              _hdOmeEnvNameRoots :: MEEnvNameRoots
              _hdOmeEnvTypeName :: MEEnvTypeName
              _hdOmeFunType :: MEFunType
              _hdOmeNamespaceCtor :: MENamespaceCtor
              _hdOmeNamespaceNameRoots :: MENamespaceNameRoots
              _hdOmeNamespaceTypeName :: MENamespaceTypeName
              _hdOmeRelationEnv :: MERelationEnv
              _hdOmeSortNameRoots :: MESortNameRoots
              _hdOmeSortTypeName :: MESortTypeName
              _tlOmeEnvNameRoots :: MEEnvNameRoots
              _tlOmeEnvTypeName :: MEEnvTypeName
              _tlOmeFunType :: MEFunType
              _tlOmeNamespaceCtor :: MENamespaceCtor
              _tlOmeNamespaceNameRoots :: MENamespaceNameRoots
              _tlOmeNamespaceTypeName :: MENamespaceTypeName
              _tlOmeRelationEnv :: MERelationEnv
              _tlOmeSortNameRoots :: MESortNameRoots
              _tlOmeSortTypeName :: MESortTypeName
              _hdIdesugared :: (TcM Core.RelationDecl)
              _hdIself :: RelationDecl
              _hdIsmeRelationEnv :: MERelationEnv
              _tlIdesugared :: (TcM [Core.RelationDecl])
              _tlIself :: RelationDecls
              _tlIsmeRelationEnv :: MERelationEnv
              _lhsOdesugared =
                  ({-# LINE 348 "src/KnotSpec/Desugaring.ag" #-}
                   (consA _hdIdesugared _tlIdesugared)
                   {-# LINE 6608 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOsmeRelationEnv =
                  ({-# LINE 230 "src/KnotSpec/Environment.ag" #-}
                   (Data.Map.unionWith (error "smeRelationEnv union") _hdIsmeRelationEnv _tlIsmeRelationEnv)
                   {-# LINE 6613 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _hdOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 6622 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 6627 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 6632 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 6637 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 6642 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 6647 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 6652 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 6657 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 6662 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 6667 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 6672 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 6677 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 6682 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 6687 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 6692 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 6697 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 6702 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 6707 "src/KnotSpec/AG.hs" #-}
                   )
              ( _hdIdesugared,_hdIself,_hdIsmeRelationEnv) =
                  hd_ _hdOmeEnvNameRoots _hdOmeEnvTypeName _hdOmeFunType _hdOmeNamespaceCtor _hdOmeNamespaceNameRoots _hdOmeNamespaceTypeName _hdOmeRelationEnv _hdOmeSortNameRoots _hdOmeSortTypeName
              ( _tlIdesugared,_tlIself,_tlIsmeRelationEnv) =
                  tl_ _tlOmeEnvNameRoots _tlOmeEnvTypeName _tlOmeFunType _tlOmeNamespaceCtor _tlOmeNamespaceNameRoots _tlOmeNamespaceTypeName _tlOmeRelationEnv _tlOmeSortNameRoots _tlOmeSortTypeName
          in  ( _lhsOdesugared,_lhsOself,_lhsOsmeRelationEnv)))
sem_RelationDecls_Nil :: T_RelationDecls
sem_RelationDecls_Nil =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOdesugared :: (TcM [Core.RelationDecl])
              _lhsOsmeRelationEnv :: MERelationEnv
              _lhsOself :: RelationDecls
              _lhsOdesugared =
                  ({-# LINE 348 "src/KnotSpec/Desugaring.ag" #-}
                   memptyA
                   {-# LINE 6731 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOsmeRelationEnv =
                  ({-# LINE 230 "src/KnotSpec/Environment.ag" #-}
                   mempty
                   {-# LINE 6736 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  []
              _lhsOself =
                  _self
          in  ( _lhsOdesugared,_lhsOself,_lhsOsmeRelationEnv)))
-- Rule --------------------------------------------------------
-- cata
sem_Rule :: Rule ->
            T_Rule
sem_Rule (Rule _ruleName _rulePremises _ruleConclusion _ruleBindings) =
    (sem_Rule_Rule _ruleName (sem_Formulas _rulePremises) (sem_Judgement _ruleConclusion) (sem_RuleBindings _ruleBindings))
-- semantic domain
type T_Rule = MEEnvNameRoots ->
              MEEnvTypeName ->
              MEFunType ->
              MENamespaceCtor ->
              MENamespaceNameRoots ->
              MENamespaceTypeName ->
              MERelationEnv ->
              MESortNameRoots ->
              MESortTypeName ->
              ( (TcM Core.Rule),Rule)
data Inh_Rule = Inh_Rule {meEnvNameRoots_Inh_Rule :: MEEnvNameRoots,meEnvTypeName_Inh_Rule :: MEEnvTypeName,meFunType_Inh_Rule :: MEFunType,meNamespaceCtor_Inh_Rule :: MENamespaceCtor,meNamespaceNameRoots_Inh_Rule :: MENamespaceNameRoots,meNamespaceTypeName_Inh_Rule :: MENamespaceTypeName,meRelationEnv_Inh_Rule :: MERelationEnv,meSortNameRoots_Inh_Rule :: MESortNameRoots,meSortTypeName_Inh_Rule :: MESortTypeName}
data Syn_Rule = Syn_Rule {desugared_Syn_Rule :: (TcM Core.Rule),self_Syn_Rule :: Rule}
wrap_Rule :: T_Rule ->
             Inh_Rule ->
             Syn_Rule
wrap_Rule sem (Inh_Rule _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName) =
    (let ( _lhsOdesugared,_lhsOself) = sem _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName
     in  (Syn_Rule _lhsOdesugared _lhsOself))
sem_Rule_Rule :: CtorName ->
                 T_Formulas ->
                 T_Judgement ->
                 T_RuleBindings ->
                 T_Rule
sem_Rule_Rule ruleName_ rulePremises_ ruleConclusion_ ruleBindings_ =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOself :: Rule
              _lhsOdesugared :: (TcM Core.Rule)
              _rulePremisesOmeEnvNameRoots :: MEEnvNameRoots
              _rulePremisesOmeEnvTypeName :: MEEnvTypeName
              _rulePremisesOmeFunType :: MEFunType
              _rulePremisesOmeNamespaceCtor :: MENamespaceCtor
              _rulePremisesOmeNamespaceNameRoots :: MENamespaceNameRoots
              _rulePremisesOmeNamespaceTypeName :: MENamespaceTypeName
              _rulePremisesOmeRelationEnv :: MERelationEnv
              _rulePremisesOmeSortNameRoots :: MESortNameRoots
              _rulePremisesOmeSortTypeName :: MESortTypeName
              _ruleConclusionOmeEnvNameRoots :: MEEnvNameRoots
              _ruleConclusionOmeEnvTypeName :: MEEnvTypeName
              _ruleConclusionOmeFunType :: MEFunType
              _ruleConclusionOmeNamespaceCtor :: MENamespaceCtor
              _ruleConclusionOmeNamespaceNameRoots :: MENamespaceNameRoots
              _ruleConclusionOmeNamespaceTypeName :: MENamespaceTypeName
              _ruleConclusionOmeRelationEnv :: MERelationEnv
              _ruleConclusionOmeSortNameRoots :: MESortNameRoots
              _ruleConclusionOmeSortTypeName :: MESortTypeName
              _ruleBindingsOmeEnvNameRoots :: MEEnvNameRoots
              _ruleBindingsOmeEnvTypeName :: MEEnvTypeName
              _ruleBindingsOmeFunType :: MEFunType
              _ruleBindingsOmeNamespaceCtor :: MENamespaceCtor
              _ruleBindingsOmeNamespaceNameRoots :: MENamespaceNameRoots
              _ruleBindingsOmeNamespaceTypeName :: MENamespaceTypeName
              _ruleBindingsOmeRelationEnv :: MERelationEnv
              _ruleBindingsOmeSortNameRoots :: MESortNameRoots
              _ruleBindingsOmeSortTypeName :: MESortTypeName
              _rulePremisesIdesugared :: (TcM [Core.Formula])
              _rulePremisesIself :: Formulas
              _ruleConclusionIdesugared :: (TcM Core.Judgement)
              _ruleConclusionIself :: Judgement
              _ruleBindingsIdesugared :: (TcM [Core.RuleBinding])
              _ruleBindingsIself :: RuleBindings
              _desugared =
                  ({-# LINE 371 "src/KnotSpec/Desugaring.ag" #-}
                   do
                     premises   <- _rulePremisesIdesugared
                     conclusion <- _ruleConclusionIdesugared
                     rbinds     <- _ruleBindingsIdesugared
                     return $
                       Core.Rule
                        (Core.CNO ruleName_)
                        []
                        premises
                        conclusion
                        rbinds
                   {-# LINE 6831 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  Rule ruleName_ _rulePremisesIself _ruleConclusionIself _ruleBindingsIself
              _lhsOself =
                  _self
              _lhsOdesugared =
                  ({-# LINE 367 "src/KnotSpec/Desugaring.ag" #-}
                   _desugared
                   {-# LINE 6840 "src/KnotSpec/AG.hs" #-}
                   )
              _rulePremisesOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 6845 "src/KnotSpec/AG.hs" #-}
                   )
              _rulePremisesOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 6850 "src/KnotSpec/AG.hs" #-}
                   )
              _rulePremisesOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 6855 "src/KnotSpec/AG.hs" #-}
                   )
              _rulePremisesOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 6860 "src/KnotSpec/AG.hs" #-}
                   )
              _rulePremisesOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 6865 "src/KnotSpec/AG.hs" #-}
                   )
              _rulePremisesOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 6870 "src/KnotSpec/AG.hs" #-}
                   )
              _rulePremisesOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 6875 "src/KnotSpec/AG.hs" #-}
                   )
              _rulePremisesOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 6880 "src/KnotSpec/AG.hs" #-}
                   )
              _rulePremisesOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 6885 "src/KnotSpec/AG.hs" #-}
                   )
              _ruleConclusionOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 6890 "src/KnotSpec/AG.hs" #-}
                   )
              _ruleConclusionOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 6895 "src/KnotSpec/AG.hs" #-}
                   )
              _ruleConclusionOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 6900 "src/KnotSpec/AG.hs" #-}
                   )
              _ruleConclusionOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 6905 "src/KnotSpec/AG.hs" #-}
                   )
              _ruleConclusionOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 6910 "src/KnotSpec/AG.hs" #-}
                   )
              _ruleConclusionOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 6915 "src/KnotSpec/AG.hs" #-}
                   )
              _ruleConclusionOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 6920 "src/KnotSpec/AG.hs" #-}
                   )
              _ruleConclusionOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 6925 "src/KnotSpec/AG.hs" #-}
                   )
              _ruleConclusionOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 6930 "src/KnotSpec/AG.hs" #-}
                   )
              _ruleBindingsOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 6935 "src/KnotSpec/AG.hs" #-}
                   )
              _ruleBindingsOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 6940 "src/KnotSpec/AG.hs" #-}
                   )
              _ruleBindingsOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 6945 "src/KnotSpec/AG.hs" #-}
                   )
              _ruleBindingsOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 6950 "src/KnotSpec/AG.hs" #-}
                   )
              _ruleBindingsOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 6955 "src/KnotSpec/AG.hs" #-}
                   )
              _ruleBindingsOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 6960 "src/KnotSpec/AG.hs" #-}
                   )
              _ruleBindingsOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 6965 "src/KnotSpec/AG.hs" #-}
                   )
              _ruleBindingsOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 6970 "src/KnotSpec/AG.hs" #-}
                   )
              _ruleBindingsOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 6975 "src/KnotSpec/AG.hs" #-}
                   )
              ( _rulePremisesIdesugared,_rulePremisesIself) =
                  rulePremises_ _rulePremisesOmeEnvNameRoots _rulePremisesOmeEnvTypeName _rulePremisesOmeFunType _rulePremisesOmeNamespaceCtor _rulePremisesOmeNamespaceNameRoots _rulePremisesOmeNamespaceTypeName _rulePremisesOmeRelationEnv _rulePremisesOmeSortNameRoots _rulePremisesOmeSortTypeName
              ( _ruleConclusionIdesugared,_ruleConclusionIself) =
                  ruleConclusion_ _ruleConclusionOmeEnvNameRoots _ruleConclusionOmeEnvTypeName _ruleConclusionOmeFunType _ruleConclusionOmeNamespaceCtor _ruleConclusionOmeNamespaceNameRoots _ruleConclusionOmeNamespaceTypeName _ruleConclusionOmeRelationEnv _ruleConclusionOmeSortNameRoots _ruleConclusionOmeSortTypeName
              ( _ruleBindingsIdesugared,_ruleBindingsIself) =
                  ruleBindings_ _ruleBindingsOmeEnvNameRoots _ruleBindingsOmeEnvTypeName _ruleBindingsOmeFunType _ruleBindingsOmeNamespaceCtor _ruleBindingsOmeNamespaceNameRoots _ruleBindingsOmeNamespaceTypeName _ruleBindingsOmeRelationEnv _ruleBindingsOmeSortNameRoots _ruleBindingsOmeSortTypeName
          in  ( _lhsOdesugared,_lhsOself)))
-- RuleBinding -------------------------------------------------
-- cata
sem_RuleBinding :: RuleBinding ->
                   T_RuleBinding
sem_RuleBinding (RuleBinding _rbMetavar _rbTerms) =
    (sem_RuleBinding_RuleBinding (sem_Name _rbMetavar) (sem_SymbolicTerms _rbTerms))
-- semantic domain
type T_RuleBinding = MEEnvNameRoots ->
                     MEEnvTypeName ->
                     MEFunType ->
                     MENamespaceCtor ->
                     MENamespaceNameRoots ->
                     MENamespaceTypeName ->
                     MERelationEnv ->
                     MESortNameRoots ->
                     MESortTypeName ->
                     ( (TcM Core.RuleBinding),RuleBinding)
data Inh_RuleBinding = Inh_RuleBinding {meEnvNameRoots_Inh_RuleBinding :: MEEnvNameRoots,meEnvTypeName_Inh_RuleBinding :: MEEnvTypeName,meFunType_Inh_RuleBinding :: MEFunType,meNamespaceCtor_Inh_RuleBinding :: MENamespaceCtor,meNamespaceNameRoots_Inh_RuleBinding :: MENamespaceNameRoots,meNamespaceTypeName_Inh_RuleBinding :: MENamespaceTypeName,meRelationEnv_Inh_RuleBinding :: MERelationEnv,meSortNameRoots_Inh_RuleBinding :: MESortNameRoots,meSortTypeName_Inh_RuleBinding :: MESortTypeName}
data Syn_RuleBinding = Syn_RuleBinding {desugared_Syn_RuleBinding :: (TcM Core.RuleBinding),self_Syn_RuleBinding :: RuleBinding}
wrap_RuleBinding :: T_RuleBinding ->
                    Inh_RuleBinding ->
                    Syn_RuleBinding
wrap_RuleBinding sem (Inh_RuleBinding _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName) =
    (let ( _lhsOdesugared,_lhsOself) = sem _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName
     in  (Syn_RuleBinding _lhsOdesugared _lhsOself))
sem_RuleBinding_RuleBinding :: T_Name ->
                               T_SymbolicTerms ->
                               T_RuleBinding
sem_RuleBinding_RuleBinding rbMetavar_ rbTerms_ =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOself :: RuleBinding
              _lhsOdesugared :: (TcM Core.RuleBinding)
              _rbMetavarOmeEnvNameRoots :: MEEnvNameRoots
              _rbMetavarOmeEnvTypeName :: MEEnvTypeName
              _rbMetavarOmeFunType :: MEFunType
              _rbMetavarOmeNamespaceCtor :: MENamespaceCtor
              _rbMetavarOmeNamespaceNameRoots :: MENamespaceNameRoots
              _rbMetavarOmeNamespaceTypeName :: MENamespaceTypeName
              _rbMetavarOmeRelationEnv :: MERelationEnv
              _rbMetavarOmeSortNameRoots :: MESortNameRoots
              _rbMetavarOmeSortTypeName :: MESortTypeName
              _rbTermsOmeEnvNameRoots :: MEEnvNameRoots
              _rbTermsOmeEnvTypeName :: MEEnvTypeName
              _rbTermsOmeFunType :: MEFunType
              _rbTermsOmeNamespaceCtor :: MENamespaceCtor
              _rbTermsOmeNamespaceNameRoots :: MENamespaceNameRoots
              _rbTermsOmeNamespaceTypeName :: MENamespaceTypeName
              _rbTermsOmeRelationEnv :: MERelationEnv
              _rbTermsOmeSortNameRoots :: MESortNameRoots
              _rbTermsOmeSortTypeName :: MESortTypeName
              _rbMetavarIcoreFieldName :: (TcM CoreFieldName)
              _rbMetavarIcoreTypeName :: (TcM CoreTypeName)
              _rbMetavarIfieldMetaBinding :: (TcM Core.FieldMetaBinding)
              _rbMetavarImetavarName :: (TcM Core.MetavarVar)
              _rbMetavarInamespaceTypeName :: (TcM Core.NamespaceTypeName)
              _rbMetavarIroot :: NameRoot
              _rbMetavarIself :: Name
              _rbMetavarIsubtreeName :: (TcM Core.SubtreeVar)
              _rbMetavarIsuffix :: String
              _rbTermsIdesugared :: (TcM [Core.SymbolicTerm])
              _rbTermsIself :: SymbolicTerms
              _desugared =
                  ({-# LINE 389 "src/KnotSpec/Desugaring.ag" #-}
                   Core.RuleBinding
                     <$> _rbMetavarImetavarName
                     <*> _rbTermsIdesugared
                   {-# LINE 7058 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  RuleBinding _rbMetavarIself _rbTermsIself
              _lhsOself =
                  _self
              _lhsOdesugared =
                  ({-# LINE 385 "src/KnotSpec/Desugaring.ag" #-}
                   _desugared
                   {-# LINE 7067 "src/KnotSpec/AG.hs" #-}
                   )
              _rbMetavarOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 7072 "src/KnotSpec/AG.hs" #-}
                   )
              _rbMetavarOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 7077 "src/KnotSpec/AG.hs" #-}
                   )
              _rbMetavarOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 7082 "src/KnotSpec/AG.hs" #-}
                   )
              _rbMetavarOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 7087 "src/KnotSpec/AG.hs" #-}
                   )
              _rbMetavarOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 7092 "src/KnotSpec/AG.hs" #-}
                   )
              _rbMetavarOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 7097 "src/KnotSpec/AG.hs" #-}
                   )
              _rbMetavarOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 7102 "src/KnotSpec/AG.hs" #-}
                   )
              _rbMetavarOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 7107 "src/KnotSpec/AG.hs" #-}
                   )
              _rbMetavarOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 7112 "src/KnotSpec/AG.hs" #-}
                   )
              _rbTermsOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 7117 "src/KnotSpec/AG.hs" #-}
                   )
              _rbTermsOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 7122 "src/KnotSpec/AG.hs" #-}
                   )
              _rbTermsOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 7127 "src/KnotSpec/AG.hs" #-}
                   )
              _rbTermsOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 7132 "src/KnotSpec/AG.hs" #-}
                   )
              _rbTermsOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 7137 "src/KnotSpec/AG.hs" #-}
                   )
              _rbTermsOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 7142 "src/KnotSpec/AG.hs" #-}
                   )
              _rbTermsOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 7147 "src/KnotSpec/AG.hs" #-}
                   )
              _rbTermsOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 7152 "src/KnotSpec/AG.hs" #-}
                   )
              _rbTermsOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 7157 "src/KnotSpec/AG.hs" #-}
                   )
              ( _rbMetavarIcoreFieldName,_rbMetavarIcoreTypeName,_rbMetavarIfieldMetaBinding,_rbMetavarImetavarName,_rbMetavarInamespaceTypeName,_rbMetavarIroot,_rbMetavarIself,_rbMetavarIsubtreeName,_rbMetavarIsuffix) =
                  rbMetavar_ _rbMetavarOmeEnvNameRoots _rbMetavarOmeEnvTypeName _rbMetavarOmeFunType _rbMetavarOmeNamespaceCtor _rbMetavarOmeNamespaceNameRoots _rbMetavarOmeNamespaceTypeName _rbMetavarOmeRelationEnv _rbMetavarOmeSortNameRoots _rbMetavarOmeSortTypeName
              ( _rbTermsIdesugared,_rbTermsIself) =
                  rbTerms_ _rbTermsOmeEnvNameRoots _rbTermsOmeEnvTypeName _rbTermsOmeFunType _rbTermsOmeNamespaceCtor _rbTermsOmeNamespaceNameRoots _rbTermsOmeNamespaceTypeName _rbTermsOmeRelationEnv _rbTermsOmeSortNameRoots _rbTermsOmeSortTypeName
          in  ( _lhsOdesugared,_lhsOself)))
-- RuleBindings ------------------------------------------------
-- cata
sem_RuleBindings :: RuleBindings ->
                    T_RuleBindings
sem_RuleBindings list =
    (Prelude.foldr sem_RuleBindings_Cons sem_RuleBindings_Nil (Prelude.map sem_RuleBinding list))
-- semantic domain
type T_RuleBindings = MEEnvNameRoots ->
                      MEEnvTypeName ->
                      MEFunType ->
                      MENamespaceCtor ->
                      MENamespaceNameRoots ->
                      MENamespaceTypeName ->
                      MERelationEnv ->
                      MESortNameRoots ->
                      MESortTypeName ->
                      ( (TcM [Core.RuleBinding]),RuleBindings)
data Inh_RuleBindings = Inh_RuleBindings {meEnvNameRoots_Inh_RuleBindings :: MEEnvNameRoots,meEnvTypeName_Inh_RuleBindings :: MEEnvTypeName,meFunType_Inh_RuleBindings :: MEFunType,meNamespaceCtor_Inh_RuleBindings :: MENamespaceCtor,meNamespaceNameRoots_Inh_RuleBindings :: MENamespaceNameRoots,meNamespaceTypeName_Inh_RuleBindings :: MENamespaceTypeName,meRelationEnv_Inh_RuleBindings :: MERelationEnv,meSortNameRoots_Inh_RuleBindings :: MESortNameRoots,meSortTypeName_Inh_RuleBindings :: MESortTypeName}
data Syn_RuleBindings = Syn_RuleBindings {desugared_Syn_RuleBindings :: (TcM [Core.RuleBinding]),self_Syn_RuleBindings :: RuleBindings}
wrap_RuleBindings :: T_RuleBindings ->
                     Inh_RuleBindings ->
                     Syn_RuleBindings
wrap_RuleBindings sem (Inh_RuleBindings _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName) =
    (let ( _lhsOdesugared,_lhsOself) = sem _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName
     in  (Syn_RuleBindings _lhsOdesugared _lhsOself))
sem_RuleBindings_Cons :: T_RuleBinding ->
                         T_RuleBindings ->
                         T_RuleBindings
sem_RuleBindings_Cons hd_ tl_ =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOdesugared :: (TcM [Core.RuleBinding])
              _lhsOself :: RuleBindings
              _hdOmeEnvNameRoots :: MEEnvNameRoots
              _hdOmeEnvTypeName :: MEEnvTypeName
              _hdOmeFunType :: MEFunType
              _hdOmeNamespaceCtor :: MENamespaceCtor
              _hdOmeNamespaceNameRoots :: MENamespaceNameRoots
              _hdOmeNamespaceTypeName :: MENamespaceTypeName
              _hdOmeRelationEnv :: MERelationEnv
              _hdOmeSortNameRoots :: MESortNameRoots
              _hdOmeSortTypeName :: MESortTypeName
              _tlOmeEnvNameRoots :: MEEnvNameRoots
              _tlOmeEnvTypeName :: MEEnvTypeName
              _tlOmeFunType :: MEFunType
              _tlOmeNamespaceCtor :: MENamespaceCtor
              _tlOmeNamespaceNameRoots :: MENamespaceNameRoots
              _tlOmeNamespaceTypeName :: MENamespaceTypeName
              _tlOmeRelationEnv :: MERelationEnv
              _tlOmeSortNameRoots :: MESortNameRoots
              _tlOmeSortTypeName :: MESortTypeName
              _hdIdesugared :: (TcM Core.RuleBinding)
              _hdIself :: RuleBinding
              _tlIdesugared :: (TcM [Core.RuleBinding])
              _tlIself :: RuleBindings
              _lhsOdesugared =
                  ({-# LINE 384 "src/KnotSpec/Desugaring.ag" #-}
                   (consA _hdIdesugared _tlIdesugared)
                   {-# LINE 7229 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _hdOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 7238 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 7243 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 7248 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 7253 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 7258 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 7263 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 7268 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 7273 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 7278 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 7283 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 7288 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 7293 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 7298 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 7303 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 7308 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 7313 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 7318 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 7323 "src/KnotSpec/AG.hs" #-}
                   )
              ( _hdIdesugared,_hdIself) =
                  hd_ _hdOmeEnvNameRoots _hdOmeEnvTypeName _hdOmeFunType _hdOmeNamespaceCtor _hdOmeNamespaceNameRoots _hdOmeNamespaceTypeName _hdOmeRelationEnv _hdOmeSortNameRoots _hdOmeSortTypeName
              ( _tlIdesugared,_tlIself) =
                  tl_ _tlOmeEnvNameRoots _tlOmeEnvTypeName _tlOmeFunType _tlOmeNamespaceCtor _tlOmeNamespaceNameRoots _tlOmeNamespaceTypeName _tlOmeRelationEnv _tlOmeSortNameRoots _tlOmeSortTypeName
          in  ( _lhsOdesugared,_lhsOself)))
sem_RuleBindings_Nil :: T_RuleBindings
sem_RuleBindings_Nil =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOdesugared :: (TcM [Core.RuleBinding])
              _lhsOself :: RuleBindings
              _lhsOdesugared =
                  ({-# LINE 384 "src/KnotSpec/Desugaring.ag" #-}
                   memptyA
                   {-# LINE 7346 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  []
              _lhsOself =
                  _self
          in  ( _lhsOdesugared,_lhsOself)))
-- Rules -------------------------------------------------------
-- cata
sem_Rules :: Rules ->
             T_Rules
sem_Rules list =
    (Prelude.foldr sem_Rules_Cons sem_Rules_Nil (Prelude.map sem_Rule list))
-- semantic domain
type T_Rules = MEEnvNameRoots ->
               MEEnvTypeName ->
               MEFunType ->
               MENamespaceCtor ->
               MENamespaceNameRoots ->
               MENamespaceTypeName ->
               MERelationEnv ->
               MESortNameRoots ->
               MESortTypeName ->
               ( (TcM [Core.Rule]),Rules)
data Inh_Rules = Inh_Rules {meEnvNameRoots_Inh_Rules :: MEEnvNameRoots,meEnvTypeName_Inh_Rules :: MEEnvTypeName,meFunType_Inh_Rules :: MEFunType,meNamespaceCtor_Inh_Rules :: MENamespaceCtor,meNamespaceNameRoots_Inh_Rules :: MENamespaceNameRoots,meNamespaceTypeName_Inh_Rules :: MENamespaceTypeName,meRelationEnv_Inh_Rules :: MERelationEnv,meSortNameRoots_Inh_Rules :: MESortNameRoots,meSortTypeName_Inh_Rules :: MESortTypeName}
data Syn_Rules = Syn_Rules {desugared_Syn_Rules :: (TcM [Core.Rule]),self_Syn_Rules :: Rules}
wrap_Rules :: T_Rules ->
              Inh_Rules ->
              Syn_Rules
wrap_Rules sem (Inh_Rules _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName) =
    (let ( _lhsOdesugared,_lhsOself) = sem _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName
     in  (Syn_Rules _lhsOdesugared _lhsOself))
sem_Rules_Cons :: T_Rule ->
                  T_Rules ->
                  T_Rules
sem_Rules_Cons hd_ tl_ =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOdesugared :: (TcM [Core.Rule])
              _lhsOself :: Rules
              _hdOmeEnvNameRoots :: MEEnvNameRoots
              _hdOmeEnvTypeName :: MEEnvTypeName
              _hdOmeFunType :: MEFunType
              _hdOmeNamespaceCtor :: MENamespaceCtor
              _hdOmeNamespaceNameRoots :: MENamespaceNameRoots
              _hdOmeNamespaceTypeName :: MENamespaceTypeName
              _hdOmeRelationEnv :: MERelationEnv
              _hdOmeSortNameRoots :: MESortNameRoots
              _hdOmeSortTypeName :: MESortTypeName
              _tlOmeEnvNameRoots :: MEEnvNameRoots
              _tlOmeEnvTypeName :: MEEnvTypeName
              _tlOmeFunType :: MEFunType
              _tlOmeNamespaceCtor :: MENamespaceCtor
              _tlOmeNamespaceNameRoots :: MENamespaceNameRoots
              _tlOmeNamespaceTypeName :: MENamespaceTypeName
              _tlOmeRelationEnv :: MERelationEnv
              _tlOmeSortNameRoots :: MESortNameRoots
              _tlOmeSortTypeName :: MESortTypeName
              _hdIdesugared :: (TcM Core.Rule)
              _hdIself :: Rule
              _tlIdesugared :: (TcM [Core.Rule])
              _tlIself :: Rules
              _lhsOdesugared =
                  ({-# LINE 366 "src/KnotSpec/Desugaring.ag" #-}
                   (consA _hdIdesugared _tlIdesugared)
                   {-# LINE 7418 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _hdOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 7427 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 7432 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 7437 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 7442 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 7447 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 7452 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 7457 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 7462 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 7467 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 7472 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 7477 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 7482 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 7487 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 7492 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 7497 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 7502 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 7507 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 7512 "src/KnotSpec/AG.hs" #-}
                   )
              ( _hdIdesugared,_hdIself) =
                  hd_ _hdOmeEnvNameRoots _hdOmeEnvTypeName _hdOmeFunType _hdOmeNamespaceCtor _hdOmeNamespaceNameRoots _hdOmeNamespaceTypeName _hdOmeRelationEnv _hdOmeSortNameRoots _hdOmeSortTypeName
              ( _tlIdesugared,_tlIself) =
                  tl_ _tlOmeEnvNameRoots _tlOmeEnvTypeName _tlOmeFunType _tlOmeNamespaceCtor _tlOmeNamespaceNameRoots _tlOmeNamespaceTypeName _tlOmeRelationEnv _tlOmeSortNameRoots _tlOmeSortTypeName
          in  ( _lhsOdesugared,_lhsOself)))
sem_Rules_Nil :: T_Rules
sem_Rules_Nil =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOdesugared :: (TcM [Core.Rule])
              _lhsOself :: Rules
              _lhsOdesugared =
                  ({-# LINE 366 "src/KnotSpec/Desugaring.ag" #-}
                   memptyA
                   {-# LINE 7535 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  []
              _lhsOself =
                  _self
          in  ( _lhsOdesugared,_lhsOself)))
-- SortDecl ----------------------------------------------------
-- cata
sem_SortDecl :: SortDecl ->
                T_SortDecl
sem_SortDecl (SortDecl _sortTypeName _sortNameRoots _sortCtors) =
    (sem_SortDecl_SortDecl (sem_TypeName _sortTypeName) (sem_NameRoots _sortNameRoots) (sem_CtorDecls _sortCtors))
-- semantic domain
type T_SortDecl = MEEnvNameRoots ->
                  MEEnvTypeName ->
                  MEFunType ->
                  MENamespaceCtor ->
                  MENamespaceNameRoots ->
                  MENamespaceTypeName ->
                  MERelationEnv ->
                  MESortNameRoots ->
                  MESortTypeName ->
                  ( (TcM DepNode),(TcM Core.SortDecl),(TcM Core.FunctionEnv),SortDecl,MENamespaceCtor,MESortNameRoots,MESortTypeName)
data Inh_SortDecl = Inh_SortDecl {meEnvNameRoots_Inh_SortDecl :: MEEnvNameRoots,meEnvTypeName_Inh_SortDecl :: MEEnvTypeName,meFunType_Inh_SortDecl :: MEFunType,meNamespaceCtor_Inh_SortDecl :: MENamespaceCtor,meNamespaceNameRoots_Inh_SortDecl :: MENamespaceNameRoots,meNamespaceTypeName_Inh_SortDecl :: MENamespaceTypeName,meRelationEnv_Inh_SortDecl :: MERelationEnv,meSortNameRoots_Inh_SortDecl :: MESortNameRoots,meSortTypeName_Inh_SortDecl :: MESortTypeName}
data Syn_SortDecl = Syn_SortDecl {dependencyGraph_Syn_SortDecl :: (TcM DepNode),desugared_Syn_SortDecl :: (TcM Core.SortDecl),sFunctionDef_Syn_SortDecl :: (TcM Core.FunctionEnv),self_Syn_SortDecl :: SortDecl,smeNamespaceCtor_Syn_SortDecl :: MENamespaceCtor,smeSortNameRoots_Syn_SortDecl :: MESortNameRoots,smeSortTypeName_Syn_SortDecl :: MESortTypeName}
wrap_SortDecl :: T_SortDecl ->
                 Inh_SortDecl ->
                 Syn_SortDecl
wrap_SortDecl sem (Inh_SortDecl _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName) =
    (let ( _lhsOdependencyGraph,_lhsOdesugared,_lhsOsFunctionDef,_lhsOself,_lhsOsmeNamespaceCtor,_lhsOsmeSortNameRoots,_lhsOsmeSortTypeName) = sem _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName
     in  (Syn_SortDecl _lhsOdependencyGraph _lhsOdesugared _lhsOsFunctionDef _lhsOself _lhsOsmeNamespaceCtor _lhsOsmeSortNameRoots _lhsOsmeSortTypeName))
sem_SortDecl_SortDecl :: T_TypeName ->
                         T_NameRoots ->
                         T_CtorDecls ->
                         T_SortDecl
sem_SortDecl_SortDecl sortTypeName_ sortNameRoots_ sortCtors_ =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOdependencyGraph :: (TcM DepNode)
              _lhsOsmeSortNameRoots :: MESortNameRoots
              _lhsOsmeSortTypeName :: MESortTypeName
              _lhsOsFunctionDef :: (TcM Core.FunctionEnv)
              _lhsOsmeNamespaceCtor :: MENamespaceCtor
              _lhsOself :: SortDecl
              _lhsOdesugared :: (TcM Core.SortDecl)
              _sortTypeNameOmeEnvNameRoots :: MEEnvNameRoots
              _sortTypeNameOmeEnvTypeName :: MEEnvTypeName
              _sortTypeNameOmeFunType :: MEFunType
              _sortTypeNameOmeNamespaceCtor :: MENamespaceCtor
              _sortTypeNameOmeNamespaceNameRoots :: MENamespaceNameRoots
              _sortTypeNameOmeNamespaceTypeName :: MENamespaceTypeName
              _sortTypeNameOmeRelationEnv :: MERelationEnv
              _sortTypeNameOmeSortNameRoots :: MESortNameRoots
              _sortTypeNameOmeSortTypeName :: MESortTypeName
              _sortCtorsOcoreSortTypeName :: (Core.SortTypeName)
              _sortCtorsOmeEnvNameRoots :: MEEnvNameRoots
              _sortCtorsOmeEnvTypeName :: MEEnvTypeName
              _sortCtorsOmeFunType :: MEFunType
              _sortCtorsOmeNamespaceCtor :: MENamespaceCtor
              _sortCtorsOmeNamespaceNameRoots :: MENamespaceNameRoots
              _sortCtorsOmeNamespaceTypeName :: MENamespaceTypeName
              _sortCtorsOmeRelationEnv :: MERelationEnv
              _sortCtorsOmeSortNameRoots :: MESortNameRoots
              _sortCtorsOmeSortTypeName :: MESortTypeName
              _sortCtorsOsortTypeName :: TypeName
              _sortTypeNameIfromTn :: String
              _sortTypeNameInamespaceTypeName :: (TcM Core.NamespaceTypeName)
              _sortTypeNameIrelationTypeName :: (TcM Core.RelationTypeName)
              _sortTypeNameIself :: TypeName
              _sortTypeNameIsortTypeName :: (TcM Core.SortTypeName)
              _sortNameRootsIself :: NameRoots
              _sortCtorsIdesugared :: (TcM [Core.CtorDecl])
              _sortCtorsInamespaceDependencies :: (TcM [Core.NamespaceTypeName])
              _sortCtorsIsFunctionDef :: (TcM Core.FunctionEnv)
              _sortCtorsIself :: CtorDecls
              _sortCtorsIsmeNamespaceCtor :: MENamespaceCtor
              _sortCtorsIsortDependencies :: (TcM [Core.SortTypeName])
              _coreSortTypeName =
                  ({-# LINE 247 "src/KnotSpec/Desugaring.ag" #-}
                   Core.STN _sortTypeNameIfromTn
                   {-# LINE 7623 "src/KnotSpec/AG.hs" #-}
                   )
              _desugared =
                  ({-# LINE 248 "src/KnotSpec/Desugaring.ag" #-}
                   Core.SortDecl
                     (_coreSortTypeName    )
                     (map (Core.NR . fromNR) _sortNameRootsIself)
                     <$> _sortCtorsIdesugared
                   {-# LINE 7631 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOdependencyGraph =
                  ({-# LINE 519 "src/KnotSpec/Desugaring.ag" #-}
                   do
                     sortDecl           <- _desugared
                     sortNames          <- _sortCtorsIsortDependencies
                     namespaceTypeNames <- _sortCtorsInamespaceDependencies
                     let typeName  = Core.STN _sortTypeNameIfromTn
                         nodeLabel = (sortDecl,
                                      Data.Set.fromList sortNames,
                                      Data.Set.fromList namespaceTypeNames)
                     return (nodeLabel,typeName,sortNames)
                   {-# LINE 7644 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOsmeSortNameRoots =
                  ({-# LINE 112 "src/KnotSpec/Environment.ag" #-}
                   Data.Map.singleton _sortTypeNameIself _sortNameRootsIself
                   {-# LINE 7649 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOsmeSortTypeName =
                  ({-# LINE 113 "src/KnotSpec/Environment.ag" #-}
                   Data.Map.fromList
                     [ (fnr,_sortTypeNameIself)
                     | fnr <- _sortNameRootsIself
                     ]
                   {-# LINE 7657 "src/KnotSpec/AG.hs" #-}
                   )
              _sortTypeName =
                  ({-# LINE 139 "src/KnotSpec/Environment.ag" #-}
                   _sortTypeNameIself
                   {-# LINE 7662 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOsFunctionDef =
                  ({-# LINE 603 "src/KnotSpec/Desugaring.ag" #-}
                   _sortCtorsIsFunctionDef
                   {-# LINE 7667 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOsmeNamespaceCtor =
                  ({-# LINE 143 "src/KnotSpec/Environment.ag" #-}
                   _sortCtorsIsmeNamespaceCtor
                   {-# LINE 7672 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  SortDecl _sortTypeNameIself _sortNameRootsIself _sortCtorsIself
              _lhsOself =
                  _self
              _lhsOdesugared =
                  ({-# LINE 171 "src/KnotSpec/Desugaring.ag" #-}
                   _desugared
                   {-# LINE 7681 "src/KnotSpec/AG.hs" #-}
                   )
              _sortTypeNameOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 7686 "src/KnotSpec/AG.hs" #-}
                   )
              _sortTypeNameOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 7691 "src/KnotSpec/AG.hs" #-}
                   )
              _sortTypeNameOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 7696 "src/KnotSpec/AG.hs" #-}
                   )
              _sortTypeNameOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 7701 "src/KnotSpec/AG.hs" #-}
                   )
              _sortTypeNameOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 7706 "src/KnotSpec/AG.hs" #-}
                   )
              _sortTypeNameOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 7711 "src/KnotSpec/AG.hs" #-}
                   )
              _sortTypeNameOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 7716 "src/KnotSpec/AG.hs" #-}
                   )
              _sortTypeNameOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 7721 "src/KnotSpec/AG.hs" #-}
                   )
              _sortTypeNameOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 7726 "src/KnotSpec/AG.hs" #-}
                   )
              _sortCtorsOcoreSortTypeName =
                  ({-# LINE 243 "src/KnotSpec/Desugaring.ag" #-}
                   _coreSortTypeName
                   {-# LINE 7731 "src/KnotSpec/AG.hs" #-}
                   )
              _sortCtorsOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 7736 "src/KnotSpec/AG.hs" #-}
                   )
              _sortCtorsOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 7741 "src/KnotSpec/AG.hs" #-}
                   )
              _sortCtorsOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 7746 "src/KnotSpec/AG.hs" #-}
                   )
              _sortCtorsOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 7751 "src/KnotSpec/AG.hs" #-}
                   )
              _sortCtorsOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 7756 "src/KnotSpec/AG.hs" #-}
                   )
              _sortCtorsOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 7761 "src/KnotSpec/AG.hs" #-}
                   )
              _sortCtorsOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 7766 "src/KnotSpec/AG.hs" #-}
                   )
              _sortCtorsOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 7771 "src/KnotSpec/AG.hs" #-}
                   )
              _sortCtorsOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 7776 "src/KnotSpec/AG.hs" #-}
                   )
              _sortCtorsOsortTypeName =
                  ({-# LINE 135 "src/KnotSpec/Environment.ag" #-}
                   _sortTypeName
                   {-# LINE 7781 "src/KnotSpec/AG.hs" #-}
                   )
              ( _sortTypeNameIfromTn,_sortTypeNameInamespaceTypeName,_sortTypeNameIrelationTypeName,_sortTypeNameIself,_sortTypeNameIsortTypeName) =
                  sortTypeName_ _sortTypeNameOmeEnvNameRoots _sortTypeNameOmeEnvTypeName _sortTypeNameOmeFunType _sortTypeNameOmeNamespaceCtor _sortTypeNameOmeNamespaceNameRoots _sortTypeNameOmeNamespaceTypeName _sortTypeNameOmeRelationEnv _sortTypeNameOmeSortNameRoots _sortTypeNameOmeSortTypeName
              ( _sortNameRootsIself) =
                  sortNameRoots_
              ( _sortCtorsIdesugared,_sortCtorsInamespaceDependencies,_sortCtorsIsFunctionDef,_sortCtorsIself,_sortCtorsIsmeNamespaceCtor,_sortCtorsIsortDependencies) =
                  sortCtors_ _sortCtorsOcoreSortTypeName _sortCtorsOmeEnvNameRoots _sortCtorsOmeEnvTypeName _sortCtorsOmeFunType _sortCtorsOmeNamespaceCtor _sortCtorsOmeNamespaceNameRoots _sortCtorsOmeNamespaceTypeName _sortCtorsOmeRelationEnv _sortCtorsOmeSortNameRoots _sortCtorsOmeSortTypeName _sortCtorsOsortTypeName
          in  ( _lhsOdependencyGraph,_lhsOdesugared,_lhsOsFunctionDef,_lhsOself,_lhsOsmeNamespaceCtor,_lhsOsmeSortNameRoots,_lhsOsmeSortTypeName)))
-- SortDecls ---------------------------------------------------
-- cata
sem_SortDecls :: SortDecls ->
                 T_SortDecls
sem_SortDecls list =
    (Prelude.foldr sem_SortDecls_Cons sem_SortDecls_Nil (Prelude.map sem_SortDecl list))
-- semantic domain
type T_SortDecls = MEEnvNameRoots ->
                   MEEnvTypeName ->
                   MEFunType ->
                   MENamespaceCtor ->
                   MENamespaceNameRoots ->
                   MENamespaceTypeName ->
                   MERelationEnv ->
                   MESortNameRoots ->
                   MESortTypeName ->
                   ( (TcM [DepNode]),(TcM Core.FunctionEnv),SortDecls,MENamespaceCtor,MESortNameRoots,MESortTypeName)
data Inh_SortDecls = Inh_SortDecls {meEnvNameRoots_Inh_SortDecls :: MEEnvNameRoots,meEnvTypeName_Inh_SortDecls :: MEEnvTypeName,meFunType_Inh_SortDecls :: MEFunType,meNamespaceCtor_Inh_SortDecls :: MENamespaceCtor,meNamespaceNameRoots_Inh_SortDecls :: MENamespaceNameRoots,meNamespaceTypeName_Inh_SortDecls :: MENamespaceTypeName,meRelationEnv_Inh_SortDecls :: MERelationEnv,meSortNameRoots_Inh_SortDecls :: MESortNameRoots,meSortTypeName_Inh_SortDecls :: MESortTypeName}
data Syn_SortDecls = Syn_SortDecls {dependencyGraph_Syn_SortDecls :: (TcM [DepNode]),sFunctionDef_Syn_SortDecls :: (TcM Core.FunctionEnv),self_Syn_SortDecls :: SortDecls,smeNamespaceCtor_Syn_SortDecls :: MENamespaceCtor,smeSortNameRoots_Syn_SortDecls :: MESortNameRoots,smeSortTypeName_Syn_SortDecls :: MESortTypeName}
wrap_SortDecls :: T_SortDecls ->
                  Inh_SortDecls ->
                  Syn_SortDecls
wrap_SortDecls sem (Inh_SortDecls _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName) =
    (let ( _lhsOdependencyGraph,_lhsOsFunctionDef,_lhsOself,_lhsOsmeNamespaceCtor,_lhsOsmeSortNameRoots,_lhsOsmeSortTypeName) = sem _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName
     in  (Syn_SortDecls _lhsOdependencyGraph _lhsOsFunctionDef _lhsOself _lhsOsmeNamespaceCtor _lhsOsmeSortNameRoots _lhsOsmeSortTypeName))
sem_SortDecls_Cons :: T_SortDecl ->
                      T_SortDecls ->
                      T_SortDecls
sem_SortDecls_Cons hd_ tl_ =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOdependencyGraph :: (TcM [DepNode])
              _lhsOsFunctionDef :: (TcM Core.FunctionEnv)
              _lhsOsmeNamespaceCtor :: MENamespaceCtor
              _lhsOsmeSortNameRoots :: MESortNameRoots
              _lhsOsmeSortTypeName :: MESortTypeName
              _lhsOself :: SortDecls
              _hdOmeEnvNameRoots :: MEEnvNameRoots
              _hdOmeEnvTypeName :: MEEnvTypeName
              _hdOmeFunType :: MEFunType
              _hdOmeNamespaceCtor :: MENamespaceCtor
              _hdOmeNamespaceNameRoots :: MENamespaceNameRoots
              _hdOmeNamespaceTypeName :: MENamespaceTypeName
              _hdOmeRelationEnv :: MERelationEnv
              _hdOmeSortNameRoots :: MESortNameRoots
              _hdOmeSortTypeName :: MESortTypeName
              _tlOmeEnvNameRoots :: MEEnvNameRoots
              _tlOmeEnvTypeName :: MEEnvTypeName
              _tlOmeFunType :: MEFunType
              _tlOmeNamespaceCtor :: MENamespaceCtor
              _tlOmeNamespaceNameRoots :: MENamespaceNameRoots
              _tlOmeNamespaceTypeName :: MENamespaceTypeName
              _tlOmeRelationEnv :: MERelationEnv
              _tlOmeSortNameRoots :: MESortNameRoots
              _tlOmeSortTypeName :: MESortTypeName
              _hdIdependencyGraph :: (TcM DepNode)
              _hdIdesugared :: (TcM Core.SortDecl)
              _hdIsFunctionDef :: (TcM Core.FunctionEnv)
              _hdIself :: SortDecl
              _hdIsmeNamespaceCtor :: MENamespaceCtor
              _hdIsmeSortNameRoots :: MESortNameRoots
              _hdIsmeSortTypeName :: MESortTypeName
              _tlIdependencyGraph :: (TcM [DepNode])
              _tlIsFunctionDef :: (TcM Core.FunctionEnv)
              _tlIself :: SortDecls
              _tlIsmeNamespaceCtor :: MENamespaceCtor
              _tlIsmeSortNameRoots :: MESortNameRoots
              _tlIsmeSortTypeName :: MESortTypeName
              _lhsOdependencyGraph =
                  ({-# LINE 514 "src/KnotSpec/Desugaring.ag" #-}
                   (consA _hdIdependencyGraph _tlIdependencyGraph)
                   {-# LINE 7868 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOsFunctionDef =
                  ({-# LINE 603 "src/KnotSpec/Desugaring.ag" #-}
                   (liftA2 (Data.Map.unionWith Data.Map.union) _hdIsFunctionDef _tlIsFunctionDef)
                   {-# LINE 7873 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOsmeNamespaceCtor =
                  ({-# LINE 143 "src/KnotSpec/Environment.ag" #-}
                   (Data.Map.unionWith (error "smeVariableCtor union") _hdIsmeNamespaceCtor _tlIsmeNamespaceCtor)
                   {-# LINE 7878 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOsmeSortNameRoots =
                  ({-# LINE 99 "src/KnotSpec/Environment.ag" #-}
                   (Data.Map.unionWith (error "smeFieldNameRoots union") _hdIsmeSortNameRoots _tlIsmeSortNameRoots)
                   {-# LINE 7883 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOsmeSortTypeName =
                  ({-# LINE 102 "src/KnotSpec/Environment.ag" #-}
                   (Data.Map.unionWith (error "smeTypeName union") _hdIsmeSortTypeName _tlIsmeSortTypeName)
                   {-# LINE 7888 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _hdOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 7897 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 7902 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 7907 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 7912 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 7917 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 7922 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 7927 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 7932 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 7937 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 7942 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 7947 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 7952 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 7957 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 7962 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 7967 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 7972 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 7977 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 7982 "src/KnotSpec/AG.hs" #-}
                   )
              ( _hdIdependencyGraph,_hdIdesugared,_hdIsFunctionDef,_hdIself,_hdIsmeNamespaceCtor,_hdIsmeSortNameRoots,_hdIsmeSortTypeName) =
                  hd_ _hdOmeEnvNameRoots _hdOmeEnvTypeName _hdOmeFunType _hdOmeNamespaceCtor _hdOmeNamespaceNameRoots _hdOmeNamespaceTypeName _hdOmeRelationEnv _hdOmeSortNameRoots _hdOmeSortTypeName
              ( _tlIdependencyGraph,_tlIsFunctionDef,_tlIself,_tlIsmeNamespaceCtor,_tlIsmeSortNameRoots,_tlIsmeSortTypeName) =
                  tl_ _tlOmeEnvNameRoots _tlOmeEnvTypeName _tlOmeFunType _tlOmeNamespaceCtor _tlOmeNamespaceNameRoots _tlOmeNamespaceTypeName _tlOmeRelationEnv _tlOmeSortNameRoots _tlOmeSortTypeName
          in  ( _lhsOdependencyGraph,_lhsOsFunctionDef,_lhsOself,_lhsOsmeNamespaceCtor,_lhsOsmeSortNameRoots,_lhsOsmeSortTypeName)))
sem_SortDecls_Nil :: T_SortDecls
sem_SortDecls_Nil =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOdependencyGraph :: (TcM [DepNode])
              _lhsOsFunctionDef :: (TcM Core.FunctionEnv)
              _lhsOsmeNamespaceCtor :: MENamespaceCtor
              _lhsOsmeSortNameRoots :: MESortNameRoots
              _lhsOsmeSortTypeName :: MESortTypeName
              _lhsOself :: SortDecls
              _lhsOdependencyGraph =
                  ({-# LINE 514 "src/KnotSpec/Desugaring.ag" #-}
                   memptyA
                   {-# LINE 8009 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOsFunctionDef =
                  ({-# LINE 603 "src/KnotSpec/Desugaring.ag" #-}
                   memptyA
                   {-# LINE 8014 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOsmeNamespaceCtor =
                  ({-# LINE 143 "src/KnotSpec/Environment.ag" #-}
                   mempty
                   {-# LINE 8019 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOsmeSortNameRoots =
                  ({-# LINE 99 "src/KnotSpec/Environment.ag" #-}
                   mempty
                   {-# LINE 8024 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOsmeSortTypeName =
                  ({-# LINE 102 "src/KnotSpec/Environment.ag" #-}
                   mempty
                   {-# LINE 8029 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  []
              _lhsOself =
                  _self
          in  ( _lhsOdependencyGraph,_lhsOsFunctionDef,_lhsOself,_lhsOsmeNamespaceCtor,_lhsOsmeSortNameRoots,_lhsOsmeSortTypeName)))
-- SymbolicTerm ------------------------------------------------
-- cata
sem_SymbolicTerm :: SymbolicTerm ->
                    T_SymbolicTerm
sem_SymbolicTerm (SymVar _stVar) =
    (sem_SymbolicTerm_SymVar (sem_Name _stVar))
sem_SymbolicTerm (SymCtorVar _stCtor _stMetavar) =
    (sem_SymbolicTerm_SymCtorVar _stCtor (sem_Name _stMetavar))
sem_SymbolicTerm (SymCtorTerm _stCtor _stFields) =
    (sem_SymbolicTerm_SymCtorTerm _stCtor (sem_SymbolicTerms _stFields))
sem_SymbolicTerm (SymSubst _stVar _stSubstitute _stSubstitutee) =
    (sem_SymbolicTerm_SymSubst (sem_Name _stVar) (sem_SymbolicTerm _stSubstitute) (sem_SymbolicTerm _stSubstitutee))
-- semantic domain
type T_SymbolicTerm = MEEnvNameRoots ->
                      MEEnvTypeName ->
                      MEFunType ->
                      MENamespaceCtor ->
                      MENamespaceNameRoots ->
                      MENamespaceTypeName ->
                      MERelationEnv ->
                      MESortNameRoots ->
                      MESortTypeName ->
                      ( (TcM Core.SymbolicTerm),SymbolicTerm)
data Inh_SymbolicTerm = Inh_SymbolicTerm {meEnvNameRoots_Inh_SymbolicTerm :: MEEnvNameRoots,meEnvTypeName_Inh_SymbolicTerm :: MEEnvTypeName,meFunType_Inh_SymbolicTerm :: MEFunType,meNamespaceCtor_Inh_SymbolicTerm :: MENamespaceCtor,meNamespaceNameRoots_Inh_SymbolicTerm :: MENamespaceNameRoots,meNamespaceTypeName_Inh_SymbolicTerm :: MENamespaceTypeName,meRelationEnv_Inh_SymbolicTerm :: MERelationEnv,meSortNameRoots_Inh_SymbolicTerm :: MESortNameRoots,meSortTypeName_Inh_SymbolicTerm :: MESortTypeName}
data Syn_SymbolicTerm = Syn_SymbolicTerm {desugared_Syn_SymbolicTerm :: (TcM Core.SymbolicTerm),self_Syn_SymbolicTerm :: SymbolicTerm}
wrap_SymbolicTerm :: T_SymbolicTerm ->
                     Inh_SymbolicTerm ->
                     Syn_SymbolicTerm
wrap_SymbolicTerm sem (Inh_SymbolicTerm _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName) =
    (let ( _lhsOdesugared,_lhsOself) = sem _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName
     in  (Syn_SymbolicTerm _lhsOdesugared _lhsOself))
sem_SymbolicTerm_SymVar :: T_Name ->
                           T_SymbolicTerm
sem_SymbolicTerm_SymVar stVar_ =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOself :: SymbolicTerm
              _lhsOdesugared :: (TcM Core.SymbolicTerm)
              _stVarOmeEnvNameRoots :: MEEnvNameRoots
              _stVarOmeEnvTypeName :: MEEnvTypeName
              _stVarOmeFunType :: MEFunType
              _stVarOmeNamespaceCtor :: MENamespaceCtor
              _stVarOmeNamespaceNameRoots :: MENamespaceNameRoots
              _stVarOmeNamespaceTypeName :: MENamespaceTypeName
              _stVarOmeRelationEnv :: MERelationEnv
              _stVarOmeSortNameRoots :: MESortNameRoots
              _stVarOmeSortTypeName :: MESortTypeName
              _stVarIcoreFieldName :: (TcM CoreFieldName)
              _stVarIcoreTypeName :: (TcM CoreTypeName)
              _stVarIfieldMetaBinding :: (TcM Core.FieldMetaBinding)
              _stVarImetavarName :: (TcM Core.MetavarVar)
              _stVarInamespaceTypeName :: (TcM Core.NamespaceTypeName)
              _stVarIroot :: NameRoot
              _stVarIself :: Name
              _stVarIsubtreeName :: (TcM Core.SubtreeVar)
              _stVarIsuffix :: String
              _desugared =
                  ({-# LINE 435 "src/KnotSpec/Desugaring.ag" #-}
                   do
                     coreFieldName <- _stVarIcoreFieldName
                     case coreFieldName of
                       FRS subtreeName -> return $ Core.SymSubtree subtreeName
                       FRN metavarName -> return $ Core.SymBinding metavarName
                   {-# LINE 8106 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  SymVar _stVarIself
              _lhsOself =
                  _self
              _lhsOdesugared =
                  ({-# LINE 431 "src/KnotSpec/Desugaring.ag" #-}
                   _desugared
                   {-# LINE 8115 "src/KnotSpec/AG.hs" #-}
                   )
              _stVarOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 8120 "src/KnotSpec/AG.hs" #-}
                   )
              _stVarOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 8125 "src/KnotSpec/AG.hs" #-}
                   )
              _stVarOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 8130 "src/KnotSpec/AG.hs" #-}
                   )
              _stVarOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 8135 "src/KnotSpec/AG.hs" #-}
                   )
              _stVarOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 8140 "src/KnotSpec/AG.hs" #-}
                   )
              _stVarOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 8145 "src/KnotSpec/AG.hs" #-}
                   )
              _stVarOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 8150 "src/KnotSpec/AG.hs" #-}
                   )
              _stVarOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 8155 "src/KnotSpec/AG.hs" #-}
                   )
              _stVarOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 8160 "src/KnotSpec/AG.hs" #-}
                   )
              ( _stVarIcoreFieldName,_stVarIcoreTypeName,_stVarIfieldMetaBinding,_stVarImetavarName,_stVarInamespaceTypeName,_stVarIroot,_stVarIself,_stVarIsubtreeName,_stVarIsuffix) =
                  stVar_ _stVarOmeEnvNameRoots _stVarOmeEnvTypeName _stVarOmeFunType _stVarOmeNamespaceCtor _stVarOmeNamespaceNameRoots _stVarOmeNamespaceTypeName _stVarOmeRelationEnv _stVarOmeSortNameRoots _stVarOmeSortTypeName
          in  ( _lhsOdesugared,_lhsOself)))
sem_SymbolicTerm_SymCtorVar :: CtorName ->
                               T_Name ->
                               T_SymbolicTerm
sem_SymbolicTerm_SymCtorVar stCtor_ stMetavar_ =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOself :: SymbolicTerm
              _lhsOdesugared :: (TcM Core.SymbolicTerm)
              _stMetavarOmeEnvNameRoots :: MEEnvNameRoots
              _stMetavarOmeEnvTypeName :: MEEnvTypeName
              _stMetavarOmeFunType :: MEFunType
              _stMetavarOmeNamespaceCtor :: MENamespaceCtor
              _stMetavarOmeNamespaceNameRoots :: MENamespaceNameRoots
              _stMetavarOmeNamespaceTypeName :: MENamespaceTypeName
              _stMetavarOmeRelationEnv :: MERelationEnv
              _stMetavarOmeSortNameRoots :: MESortNameRoots
              _stMetavarOmeSortTypeName :: MESortTypeName
              _stMetavarIcoreFieldName :: (TcM CoreFieldName)
              _stMetavarIcoreTypeName :: (TcM CoreTypeName)
              _stMetavarIfieldMetaBinding :: (TcM Core.FieldMetaBinding)
              _stMetavarImetavarName :: (TcM Core.MetavarVar)
              _stMetavarInamespaceTypeName :: (TcM Core.NamespaceTypeName)
              _stMetavarIroot :: NameRoot
              _stMetavarIself :: Name
              _stMetavarIsubtreeName :: (TcM Core.SubtreeVar)
              _stMetavarIsuffix :: String
              _desugared =
                  ({-# LINE 442 "src/KnotSpec/Desugaring.ag" #-}
                   Core.SymCtorVar
                     <$> pure (Core.CNO stCtor_)
                     <*> _stMetavarImetavarName
                   {-# LINE 8203 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  SymCtorVar stCtor_ _stMetavarIself
              _lhsOself =
                  _self
              _lhsOdesugared =
                  ({-# LINE 431 "src/KnotSpec/Desugaring.ag" #-}
                   _desugared
                   {-# LINE 8212 "src/KnotSpec/AG.hs" #-}
                   )
              _stMetavarOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 8217 "src/KnotSpec/AG.hs" #-}
                   )
              _stMetavarOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 8222 "src/KnotSpec/AG.hs" #-}
                   )
              _stMetavarOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 8227 "src/KnotSpec/AG.hs" #-}
                   )
              _stMetavarOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 8232 "src/KnotSpec/AG.hs" #-}
                   )
              _stMetavarOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 8237 "src/KnotSpec/AG.hs" #-}
                   )
              _stMetavarOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 8242 "src/KnotSpec/AG.hs" #-}
                   )
              _stMetavarOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 8247 "src/KnotSpec/AG.hs" #-}
                   )
              _stMetavarOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 8252 "src/KnotSpec/AG.hs" #-}
                   )
              _stMetavarOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 8257 "src/KnotSpec/AG.hs" #-}
                   )
              ( _stMetavarIcoreFieldName,_stMetavarIcoreTypeName,_stMetavarIfieldMetaBinding,_stMetavarImetavarName,_stMetavarInamespaceTypeName,_stMetavarIroot,_stMetavarIself,_stMetavarIsubtreeName,_stMetavarIsuffix) =
                  stMetavar_ _stMetavarOmeEnvNameRoots _stMetavarOmeEnvTypeName _stMetavarOmeFunType _stMetavarOmeNamespaceCtor _stMetavarOmeNamespaceNameRoots _stMetavarOmeNamespaceTypeName _stMetavarOmeRelationEnv _stMetavarOmeSortNameRoots _stMetavarOmeSortTypeName
          in  ( _lhsOdesugared,_lhsOself)))
sem_SymbolicTerm_SymCtorTerm :: CtorName ->
                                T_SymbolicTerms ->
                                T_SymbolicTerm
sem_SymbolicTerm_SymCtorTerm stCtor_ stFields_ =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOself :: SymbolicTerm
              _lhsOdesugared :: (TcM Core.SymbolicTerm)
              _stFieldsOmeEnvNameRoots :: MEEnvNameRoots
              _stFieldsOmeEnvTypeName :: MEEnvTypeName
              _stFieldsOmeFunType :: MEFunType
              _stFieldsOmeNamespaceCtor :: MENamespaceCtor
              _stFieldsOmeNamespaceNameRoots :: MENamespaceNameRoots
              _stFieldsOmeNamespaceTypeName :: MENamespaceTypeName
              _stFieldsOmeRelationEnv :: MERelationEnv
              _stFieldsOmeSortNameRoots :: MESortNameRoots
              _stFieldsOmeSortTypeName :: MESortTypeName
              _stFieldsIdesugared :: (TcM [Core.SymbolicTerm])
              _stFieldsIself :: SymbolicTerms
              _desugared =
                  ({-# LINE 447 "src/KnotSpec/Desugaring.ag" #-}
                   Core.SymCtorTerm
                     <$> pure (Core.CNO stCtor_)
                     <*> _stFieldsIdesugared
                   {-# LINE 8293 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  SymCtorTerm stCtor_ _stFieldsIself
              _lhsOself =
                  _self
              _lhsOdesugared =
                  ({-# LINE 431 "src/KnotSpec/Desugaring.ag" #-}
                   _desugared
                   {-# LINE 8302 "src/KnotSpec/AG.hs" #-}
                   )
              _stFieldsOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 8307 "src/KnotSpec/AG.hs" #-}
                   )
              _stFieldsOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 8312 "src/KnotSpec/AG.hs" #-}
                   )
              _stFieldsOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 8317 "src/KnotSpec/AG.hs" #-}
                   )
              _stFieldsOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 8322 "src/KnotSpec/AG.hs" #-}
                   )
              _stFieldsOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 8327 "src/KnotSpec/AG.hs" #-}
                   )
              _stFieldsOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 8332 "src/KnotSpec/AG.hs" #-}
                   )
              _stFieldsOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 8337 "src/KnotSpec/AG.hs" #-}
                   )
              _stFieldsOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 8342 "src/KnotSpec/AG.hs" #-}
                   )
              _stFieldsOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 8347 "src/KnotSpec/AG.hs" #-}
                   )
              ( _stFieldsIdesugared,_stFieldsIself) =
                  stFields_ _stFieldsOmeEnvNameRoots _stFieldsOmeEnvTypeName _stFieldsOmeFunType _stFieldsOmeNamespaceCtor _stFieldsOmeNamespaceNameRoots _stFieldsOmeNamespaceTypeName _stFieldsOmeRelationEnv _stFieldsOmeSortNameRoots _stFieldsOmeSortTypeName
          in  ( _lhsOdesugared,_lhsOself)))
sem_SymbolicTerm_SymSubst :: T_Name ->
                             T_SymbolicTerm ->
                             T_SymbolicTerm ->
                             T_SymbolicTerm
sem_SymbolicTerm_SymSubst stVar_ stSubstitute_ stSubstitutee_ =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOself :: SymbolicTerm
              _lhsOdesugared :: (TcM Core.SymbolicTerm)
              _stVarOmeEnvNameRoots :: MEEnvNameRoots
              _stVarOmeEnvTypeName :: MEEnvTypeName
              _stVarOmeFunType :: MEFunType
              _stVarOmeNamespaceCtor :: MENamespaceCtor
              _stVarOmeNamespaceNameRoots :: MENamespaceNameRoots
              _stVarOmeNamespaceTypeName :: MENamespaceTypeName
              _stVarOmeRelationEnv :: MERelationEnv
              _stVarOmeSortNameRoots :: MESortNameRoots
              _stVarOmeSortTypeName :: MESortTypeName
              _stSubstituteOmeEnvNameRoots :: MEEnvNameRoots
              _stSubstituteOmeEnvTypeName :: MEEnvTypeName
              _stSubstituteOmeFunType :: MEFunType
              _stSubstituteOmeNamespaceCtor :: MENamespaceCtor
              _stSubstituteOmeNamespaceNameRoots :: MENamespaceNameRoots
              _stSubstituteOmeNamespaceTypeName :: MENamespaceTypeName
              _stSubstituteOmeRelationEnv :: MERelationEnv
              _stSubstituteOmeSortNameRoots :: MESortNameRoots
              _stSubstituteOmeSortTypeName :: MESortTypeName
              _stSubstituteeOmeEnvNameRoots :: MEEnvNameRoots
              _stSubstituteeOmeEnvTypeName :: MEEnvTypeName
              _stSubstituteeOmeFunType :: MEFunType
              _stSubstituteeOmeNamespaceCtor :: MENamespaceCtor
              _stSubstituteeOmeNamespaceNameRoots :: MENamespaceNameRoots
              _stSubstituteeOmeNamespaceTypeName :: MENamespaceTypeName
              _stSubstituteeOmeRelationEnv :: MERelationEnv
              _stSubstituteeOmeSortNameRoots :: MESortNameRoots
              _stSubstituteeOmeSortTypeName :: MESortTypeName
              _stVarIcoreFieldName :: (TcM CoreFieldName)
              _stVarIcoreTypeName :: (TcM CoreTypeName)
              _stVarIfieldMetaBinding :: (TcM Core.FieldMetaBinding)
              _stVarImetavarName :: (TcM Core.MetavarVar)
              _stVarInamespaceTypeName :: (TcM Core.NamespaceTypeName)
              _stVarIroot :: NameRoot
              _stVarIself :: Name
              _stVarIsubtreeName :: (TcM Core.SubtreeVar)
              _stVarIsuffix :: String
              _stSubstituteIdesugared :: (TcM Core.SymbolicTerm)
              _stSubstituteIself :: SymbolicTerm
              _stSubstituteeIdesugared :: (TcM Core.SymbolicTerm)
              _stSubstituteeIself :: SymbolicTerm
              _desugared =
                  ({-# LINE 452 "src/KnotSpec/Desugaring.ag" #-}
                   Core.SymSubst
                     <$> _stVarImetavarName
                     <*> _stSubstituteIdesugared
                     <*> _stSubstituteeIdesugared
                   {-# LINE 8414 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  SymSubst _stVarIself _stSubstituteIself _stSubstituteeIself
              _lhsOself =
                  _self
              _lhsOdesugared =
                  ({-# LINE 431 "src/KnotSpec/Desugaring.ag" #-}
                   _desugared
                   {-# LINE 8423 "src/KnotSpec/AG.hs" #-}
                   )
              _stVarOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 8428 "src/KnotSpec/AG.hs" #-}
                   )
              _stVarOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 8433 "src/KnotSpec/AG.hs" #-}
                   )
              _stVarOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 8438 "src/KnotSpec/AG.hs" #-}
                   )
              _stVarOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 8443 "src/KnotSpec/AG.hs" #-}
                   )
              _stVarOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 8448 "src/KnotSpec/AG.hs" #-}
                   )
              _stVarOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 8453 "src/KnotSpec/AG.hs" #-}
                   )
              _stVarOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 8458 "src/KnotSpec/AG.hs" #-}
                   )
              _stVarOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 8463 "src/KnotSpec/AG.hs" #-}
                   )
              _stVarOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 8468 "src/KnotSpec/AG.hs" #-}
                   )
              _stSubstituteOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 8473 "src/KnotSpec/AG.hs" #-}
                   )
              _stSubstituteOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 8478 "src/KnotSpec/AG.hs" #-}
                   )
              _stSubstituteOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 8483 "src/KnotSpec/AG.hs" #-}
                   )
              _stSubstituteOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 8488 "src/KnotSpec/AG.hs" #-}
                   )
              _stSubstituteOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 8493 "src/KnotSpec/AG.hs" #-}
                   )
              _stSubstituteOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 8498 "src/KnotSpec/AG.hs" #-}
                   )
              _stSubstituteOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 8503 "src/KnotSpec/AG.hs" #-}
                   )
              _stSubstituteOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 8508 "src/KnotSpec/AG.hs" #-}
                   )
              _stSubstituteOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 8513 "src/KnotSpec/AG.hs" #-}
                   )
              _stSubstituteeOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 8518 "src/KnotSpec/AG.hs" #-}
                   )
              _stSubstituteeOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 8523 "src/KnotSpec/AG.hs" #-}
                   )
              _stSubstituteeOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 8528 "src/KnotSpec/AG.hs" #-}
                   )
              _stSubstituteeOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 8533 "src/KnotSpec/AG.hs" #-}
                   )
              _stSubstituteeOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 8538 "src/KnotSpec/AG.hs" #-}
                   )
              _stSubstituteeOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 8543 "src/KnotSpec/AG.hs" #-}
                   )
              _stSubstituteeOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 8548 "src/KnotSpec/AG.hs" #-}
                   )
              _stSubstituteeOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 8553 "src/KnotSpec/AG.hs" #-}
                   )
              _stSubstituteeOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 8558 "src/KnotSpec/AG.hs" #-}
                   )
              ( _stVarIcoreFieldName,_stVarIcoreTypeName,_stVarIfieldMetaBinding,_stVarImetavarName,_stVarInamespaceTypeName,_stVarIroot,_stVarIself,_stVarIsubtreeName,_stVarIsuffix) =
                  stVar_ _stVarOmeEnvNameRoots _stVarOmeEnvTypeName _stVarOmeFunType _stVarOmeNamespaceCtor _stVarOmeNamespaceNameRoots _stVarOmeNamespaceTypeName _stVarOmeRelationEnv _stVarOmeSortNameRoots _stVarOmeSortTypeName
              ( _stSubstituteIdesugared,_stSubstituteIself) =
                  stSubstitute_ _stSubstituteOmeEnvNameRoots _stSubstituteOmeEnvTypeName _stSubstituteOmeFunType _stSubstituteOmeNamespaceCtor _stSubstituteOmeNamespaceNameRoots _stSubstituteOmeNamespaceTypeName _stSubstituteOmeRelationEnv _stSubstituteOmeSortNameRoots _stSubstituteOmeSortTypeName
              ( _stSubstituteeIdesugared,_stSubstituteeIself) =
                  stSubstitutee_ _stSubstituteeOmeEnvNameRoots _stSubstituteeOmeEnvTypeName _stSubstituteeOmeFunType _stSubstituteeOmeNamespaceCtor _stSubstituteeOmeNamespaceNameRoots _stSubstituteeOmeNamespaceTypeName _stSubstituteeOmeRelationEnv _stSubstituteeOmeSortNameRoots _stSubstituteeOmeSortTypeName
          in  ( _lhsOdesugared,_lhsOself)))
-- SymbolicTerms -----------------------------------------------
-- cata
sem_SymbolicTerms :: SymbolicTerms ->
                     T_SymbolicTerms
sem_SymbolicTerms list =
    (Prelude.foldr sem_SymbolicTerms_Cons sem_SymbolicTerms_Nil (Prelude.map sem_SymbolicTerm list))
-- semantic domain
type T_SymbolicTerms = MEEnvNameRoots ->
                       MEEnvTypeName ->
                       MEFunType ->
                       MENamespaceCtor ->
                       MENamespaceNameRoots ->
                       MENamespaceTypeName ->
                       MERelationEnv ->
                       MESortNameRoots ->
                       MESortTypeName ->
                       ( (TcM [Core.SymbolicTerm]),SymbolicTerms)
data Inh_SymbolicTerms = Inh_SymbolicTerms {meEnvNameRoots_Inh_SymbolicTerms :: MEEnvNameRoots,meEnvTypeName_Inh_SymbolicTerms :: MEEnvTypeName,meFunType_Inh_SymbolicTerms :: MEFunType,meNamespaceCtor_Inh_SymbolicTerms :: MENamespaceCtor,meNamespaceNameRoots_Inh_SymbolicTerms :: MENamespaceNameRoots,meNamespaceTypeName_Inh_SymbolicTerms :: MENamespaceTypeName,meRelationEnv_Inh_SymbolicTerms :: MERelationEnv,meSortNameRoots_Inh_SymbolicTerms :: MESortNameRoots,meSortTypeName_Inh_SymbolicTerms :: MESortTypeName}
data Syn_SymbolicTerms = Syn_SymbolicTerms {desugared_Syn_SymbolicTerms :: (TcM [Core.SymbolicTerm]),self_Syn_SymbolicTerms :: SymbolicTerms}
wrap_SymbolicTerms :: T_SymbolicTerms ->
                      Inh_SymbolicTerms ->
                      Syn_SymbolicTerms
wrap_SymbolicTerms sem (Inh_SymbolicTerms _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName) =
    (let ( _lhsOdesugared,_lhsOself) = sem _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName
     in  (Syn_SymbolicTerms _lhsOdesugared _lhsOself))
sem_SymbolicTerms_Cons :: T_SymbolicTerm ->
                          T_SymbolicTerms ->
                          T_SymbolicTerms
sem_SymbolicTerms_Cons hd_ tl_ =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOdesugared :: (TcM [Core.SymbolicTerm])
              _lhsOself :: SymbolicTerms
              _hdOmeEnvNameRoots :: MEEnvNameRoots
              _hdOmeEnvTypeName :: MEEnvTypeName
              _hdOmeFunType :: MEFunType
              _hdOmeNamespaceCtor :: MENamespaceCtor
              _hdOmeNamespaceNameRoots :: MENamespaceNameRoots
              _hdOmeNamespaceTypeName :: MENamespaceTypeName
              _hdOmeRelationEnv :: MERelationEnv
              _hdOmeSortNameRoots :: MESortNameRoots
              _hdOmeSortTypeName :: MESortTypeName
              _tlOmeEnvNameRoots :: MEEnvNameRoots
              _tlOmeEnvTypeName :: MEEnvTypeName
              _tlOmeFunType :: MEFunType
              _tlOmeNamespaceCtor :: MENamespaceCtor
              _tlOmeNamespaceNameRoots :: MENamespaceNameRoots
              _tlOmeNamespaceTypeName :: MENamespaceTypeName
              _tlOmeRelationEnv :: MERelationEnv
              _tlOmeSortNameRoots :: MESortNameRoots
              _tlOmeSortTypeName :: MESortTypeName
              _hdIdesugared :: (TcM Core.SymbolicTerm)
              _hdIself :: SymbolicTerm
              _tlIdesugared :: (TcM [Core.SymbolicTerm])
              _tlIself :: SymbolicTerms
              _lhsOdesugared =
                  ({-# LINE 430 "src/KnotSpec/Desugaring.ag" #-}
                   (consA _hdIdesugared _tlIdesugared)
                   {-# LINE 8632 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _hdOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 8641 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 8646 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 8651 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 8656 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 8661 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 8666 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 8671 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 8676 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 8681 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 8686 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 8691 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 8696 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 8701 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 8706 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 8711 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 8716 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 8721 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 8726 "src/KnotSpec/AG.hs" #-}
                   )
              ( _hdIdesugared,_hdIself) =
                  hd_ _hdOmeEnvNameRoots _hdOmeEnvTypeName _hdOmeFunType _hdOmeNamespaceCtor _hdOmeNamespaceNameRoots _hdOmeNamespaceTypeName _hdOmeRelationEnv _hdOmeSortNameRoots _hdOmeSortTypeName
              ( _tlIdesugared,_tlIself) =
                  tl_ _tlOmeEnvNameRoots _tlOmeEnvTypeName _tlOmeFunType _tlOmeNamespaceCtor _tlOmeNamespaceNameRoots _tlOmeNamespaceTypeName _tlOmeRelationEnv _tlOmeSortNameRoots _tlOmeSortTypeName
          in  ( _lhsOdesugared,_lhsOself)))
sem_SymbolicTerms_Nil :: T_SymbolicTerms
sem_SymbolicTerms_Nil =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOdesugared :: (TcM [Core.SymbolicTerm])
              _lhsOself :: SymbolicTerms
              _lhsOdesugared =
                  ({-# LINE 430 "src/KnotSpec/Desugaring.ag" #-}
                   memptyA
                   {-# LINE 8749 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  []
              _lhsOself =
                  _self
          in  ( _lhsOdesugared,_lhsOself)))
-- TermSpec ----------------------------------------------------
-- cata
sem_TermSpec :: TermSpec ->
                T_TermSpec
sem_TermSpec (TermSpec _tsNamespaceDecls _tsSortDecls _tsFunDecls _tsEnvDecls _tsRelDecls) =
    (sem_TermSpec_TermSpec (sem_NamespaceDecls _tsNamespaceDecls) (sem_SortDecls _tsSortDecls) (sem_FunDecls _tsFunDecls) (sem_EnvDecls _tsEnvDecls) (sem_RelationDecls _tsRelDecls))
-- semantic domain
type T_TermSpec = ( (TcM Core.TermSpec),MetaEnvironments,TermSpec)
data Inh_TermSpec = Inh_TermSpec {}
data Syn_TermSpec = Syn_TermSpec {desugared_Syn_TermSpec :: (TcM Core.TermSpec),metaEnvironments_Syn_TermSpec :: MetaEnvironments,self_Syn_TermSpec :: TermSpec}
wrap_TermSpec :: T_TermSpec ->
                 Inh_TermSpec ->
                 Syn_TermSpec
wrap_TermSpec sem (Inh_TermSpec) =
    (let ( _lhsOdesugared,_lhsOmetaEnvironments,_lhsOself) = sem
     in  (Syn_TermSpec _lhsOdesugared _lhsOmetaEnvironments _lhsOself))
sem_TermSpec_TermSpec :: T_NamespaceDecls ->
                         T_SortDecls ->
                         T_FunDecls ->
                         T_EnvDecls ->
                         T_RelationDecls ->
                         T_TermSpec
sem_TermSpec_TermSpec tsNamespaceDecls_ tsSortDecls_ tsFunDecls_ tsEnvDecls_ tsRelDecls_ =
    (let _lhsOdesugared :: (TcM Core.TermSpec)
         _lhsOself :: TermSpec
         _lhsOmetaEnvironments :: MetaEnvironments
         _tsNamespaceDeclsOmeEnvNameRoots :: MEEnvNameRoots
         _tsNamespaceDeclsOmeEnvTypeName :: MEEnvTypeName
         _tsNamespaceDeclsOmeFunType :: MEFunType
         _tsNamespaceDeclsOmeNamespaceCtor :: MENamespaceCtor
         _tsNamespaceDeclsOmeNamespaceNameRoots :: MENamespaceNameRoots
         _tsNamespaceDeclsOmeNamespaceTypeName :: MENamespaceTypeName
         _tsNamespaceDeclsOmeRelationEnv :: MERelationEnv
         _tsNamespaceDeclsOmeSortNameRoots :: MESortNameRoots
         _tsNamespaceDeclsOmeSortTypeName :: MESortTypeName
         _tsSortDeclsOmeEnvNameRoots :: MEEnvNameRoots
         _tsSortDeclsOmeEnvTypeName :: MEEnvTypeName
         _tsSortDeclsOmeFunType :: MEFunType
         _tsSortDeclsOmeNamespaceCtor :: MENamespaceCtor
         _tsSortDeclsOmeNamespaceNameRoots :: MENamespaceNameRoots
         _tsSortDeclsOmeNamespaceTypeName :: MENamespaceTypeName
         _tsSortDeclsOmeRelationEnv :: MERelationEnv
         _tsSortDeclsOmeSortNameRoots :: MESortNameRoots
         _tsSortDeclsOmeSortTypeName :: MESortTypeName
         _tsFunDeclsOmeEnvNameRoots :: MEEnvNameRoots
         _tsFunDeclsOmeEnvTypeName :: MEEnvTypeName
         _tsFunDeclsOmeFunType :: MEFunType
         _tsFunDeclsOmeNamespaceCtor :: MENamespaceCtor
         _tsFunDeclsOmeNamespaceNameRoots :: MENamespaceNameRoots
         _tsFunDeclsOmeNamespaceTypeName :: MENamespaceTypeName
         _tsFunDeclsOmeRelationEnv :: MERelationEnv
         _tsFunDeclsOmeSortNameRoots :: MESortNameRoots
         _tsFunDeclsOmeSortTypeName :: MESortTypeName
         _tsEnvDeclsOmeEnvNameRoots :: MEEnvNameRoots
         _tsEnvDeclsOmeEnvTypeName :: MEEnvTypeName
         _tsEnvDeclsOmeFunType :: MEFunType
         _tsEnvDeclsOmeNamespaceCtor :: MENamespaceCtor
         _tsEnvDeclsOmeNamespaceNameRoots :: MENamespaceNameRoots
         _tsEnvDeclsOmeNamespaceTypeName :: MENamespaceTypeName
         _tsEnvDeclsOmeRelationEnv :: MERelationEnv
         _tsEnvDeclsOmeSortNameRoots :: MESortNameRoots
         _tsEnvDeclsOmeSortTypeName :: MESortTypeName
         _tsRelDeclsOmeEnvNameRoots :: MEEnvNameRoots
         _tsRelDeclsOmeEnvTypeName :: MEEnvTypeName
         _tsRelDeclsOmeFunType :: MEFunType
         _tsRelDeclsOmeNamespaceCtor :: MENamespaceCtor
         _tsRelDeclsOmeNamespaceNameRoots :: MENamespaceNameRoots
         _tsRelDeclsOmeNamespaceTypeName :: MENamespaceTypeName
         _tsRelDeclsOmeRelationEnv :: MERelationEnv
         _tsRelDeclsOmeSortNameRoots :: MESortNameRoots
         _tsRelDeclsOmeSortTypeName :: MESortTypeName
         _tsNamespaceDeclsIdesugared :: (TcM [Core.NamespaceDecl])
         _tsNamespaceDeclsIself :: NamespaceDecls
         _tsNamespaceDeclsIsmeNamespaceNameRoots :: MENamespaceNameRoots
         _tsSortDeclsIdependencyGraph :: (TcM [DepNode])
         _tsSortDeclsIsFunctionDef :: (TcM Core.FunctionEnv)
         _tsSortDeclsIself :: SortDecls
         _tsSortDeclsIsmeNamespaceCtor :: MENamespaceCtor
         _tsSortDeclsIsmeSortNameRoots :: MESortNameRoots
         _tsSortDeclsIsmeSortTypeName :: MESortTypeName
         _tsFunDeclsIdesugared :: (TcM [Core.FunDecl])
         _tsFunDeclsIsFunctionDef :: (TcM Core.FunctionEnv)
         _tsFunDeclsIself :: FunDecls
         _tsFunDeclsIsmeFunType :: MEFunType
         _tsEnvDeclsIdesugared :: (TcM [Core.EnvDecl])
         _tsEnvDeclsIself :: EnvDecls
         _tsEnvDeclsIsmeEnvNameRoots :: MEEnvNameRoots
         _tsRelDeclsIdesugared :: (TcM [Core.RelationDecl])
         _tsRelDeclsIself :: RelationDecls
         _tsRelDeclsIsmeRelationEnv :: MERelationEnv
         _lhsOdesugared =
             ({-# LINE 186 "src/KnotSpec/Desugaring.ag" #-}
              Core.TermSpec
                <$> _tsNamespaceDeclsIdesugared
                <*> _tsSortDeclsIsFunctionDef
                <*> (dependencyAnalysis <$> _tsSortDeclsIdependencyGraph)
                <*> (do
                       fds <- _tsFunDeclsIdesugared
                       return [ Core.FunGroupDecl
                                  fgn
                                  (Core.groupName [Core.fdSource fd])
                                  [(Core.fdSource fd, [fd])]
                              | fd <- fds
                              , let fgn = Core.FGN (Core.fnName $ Core.fdName fd)
                              ]
                    )
                <*> _tsEnvDeclsIdesugared
                <*> _tsRelDeclsIdesugared
              {-# LINE 8864 "src/KnotSpec/AG.hs" #-}
              )
         _metaEnvironments =
             ({-# LINE 49 "src/KnotSpec/Environment.ag" #-}
              MetaEnvironments
                _meNamespaceNameRoots
                _meNamespaceTypeName
                _meSortNameRoots
                _meSortTypeName
                _meNamespaceCtor
                _meEnvNameRoots
                _meEnvTypeName
                _meFunType
                _meRelationEnv
              {-# LINE 8878 "src/KnotSpec/AG.hs" #-}
              )
         _meNamespaceNameRoots =
             ({-# LINE 83 "src/KnotSpec/Environment.ag" #-}
              _tsNamespaceDeclsIsmeNamespaceNameRoots
              {-# LINE 8883 "src/KnotSpec/AG.hs" #-}
              )
         _meNamespaceTypeName =
             ({-# LINE 85 "src/KnotSpec/Environment.ag" #-}
              Data.Map.fromList
                [ (nameRoot,typeName)
                | (typeName,nameRoots) <-
                    Data.Map.toList _tsNamespaceDeclsIsmeNamespaceNameRoots
                , nameRoot <- nameRoots
                ]
              {-# LINE 8893 "src/KnotSpec/AG.hs" #-}
              )
         _meSortNameRoots =
             ({-# LINE 120 "src/KnotSpec/Environment.ag" #-}
              _tsSortDeclsIsmeSortNameRoots
              {-# LINE 8898 "src/KnotSpec/AG.hs" #-}
              )
         _meSortTypeName =
             ({-# LINE 122 "src/KnotSpec/Environment.ag" #-}
              Data.Map.fromList
                [ (nameRoot,typeName)
                | (typeName,nameRoots) <- Data.Map.toList _tsSortDeclsIsmeSortNameRoots
                , nameRoot <- nameRoots
                ]
              {-# LINE 8907 "src/KnotSpec/AG.hs" #-}
              )
         _meNamespaceCtor =
             ({-# LINE 165 "src/KnotSpec/Environment.ag" #-}
              _tsSortDeclsIsmeNamespaceCtor
              {-# LINE 8912 "src/KnotSpec/AG.hs" #-}
              )
         _meFunType =
             ({-# LINE 187 "src/KnotSpec/Environment.ag" #-}
              _tsFunDeclsIsmeFunType
              {-# LINE 8917 "src/KnotSpec/AG.hs" #-}
              )
         _meEnvNameRoots =
             ({-# LINE 215 "src/KnotSpec/Environment.ag" #-}
              _tsEnvDeclsIsmeEnvNameRoots
              {-# LINE 8922 "src/KnotSpec/AG.hs" #-}
              )
         _meEnvTypeName =
             ({-# LINE 217 "src/KnotSpec/Environment.ag" #-}
              Data.Map.fromList
                [ (nameRoot,typeName)
                | (typeName,nameRoots) <- Data.Map.toList _tsEnvDeclsIsmeEnvNameRoots
                , nameRoot <- nameRoots
                ]
              {-# LINE 8931 "src/KnotSpec/AG.hs" #-}
              )
         _meRelationEnv =
             ({-# LINE 246 "src/KnotSpec/Environment.ag" #-}
              _tsRelDeclsIsmeRelationEnv
              {-# LINE 8936 "src/KnotSpec/AG.hs" #-}
              )
         _self =
             TermSpec _tsNamespaceDeclsIself _tsSortDeclsIself _tsFunDeclsIself _tsEnvDeclsIself _tsRelDeclsIself
         _lhsOself =
             _self
         _lhsOmetaEnvironments =
             ({-# LINE 45 "src/KnotSpec/Environment.ag" #-}
              _metaEnvironments
              {-# LINE 8945 "src/KnotSpec/AG.hs" #-}
              )
         _tsNamespaceDeclsOmeEnvNameRoots =
             ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
              _meEnvNameRoots
              {-# LINE 8950 "src/KnotSpec/AG.hs" #-}
              )
         _tsNamespaceDeclsOmeEnvTypeName =
             ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
              _meEnvTypeName
              {-# LINE 8955 "src/KnotSpec/AG.hs" #-}
              )
         _tsNamespaceDeclsOmeFunType =
             ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
              _meFunType
              {-# LINE 8960 "src/KnotSpec/AG.hs" #-}
              )
         _tsNamespaceDeclsOmeNamespaceCtor =
             ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
              _meNamespaceCtor
              {-# LINE 8965 "src/KnotSpec/AG.hs" #-}
              )
         _tsNamespaceDeclsOmeNamespaceNameRoots =
             ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
              _meNamespaceNameRoots
              {-# LINE 8970 "src/KnotSpec/AG.hs" #-}
              )
         _tsNamespaceDeclsOmeNamespaceTypeName =
             ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
              _meNamespaceTypeName
              {-# LINE 8975 "src/KnotSpec/AG.hs" #-}
              )
         _tsNamespaceDeclsOmeRelationEnv =
             ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
              _meRelationEnv
              {-# LINE 8980 "src/KnotSpec/AG.hs" #-}
              )
         _tsNamespaceDeclsOmeSortNameRoots =
             ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
              _meSortNameRoots
              {-# LINE 8985 "src/KnotSpec/AG.hs" #-}
              )
         _tsNamespaceDeclsOmeSortTypeName =
             ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
              _meSortTypeName
              {-# LINE 8990 "src/KnotSpec/AG.hs" #-}
              )
         _tsSortDeclsOmeEnvNameRoots =
             ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
              _meEnvNameRoots
              {-# LINE 8995 "src/KnotSpec/AG.hs" #-}
              )
         _tsSortDeclsOmeEnvTypeName =
             ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
              _meEnvTypeName
              {-# LINE 9000 "src/KnotSpec/AG.hs" #-}
              )
         _tsSortDeclsOmeFunType =
             ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
              _meFunType
              {-# LINE 9005 "src/KnotSpec/AG.hs" #-}
              )
         _tsSortDeclsOmeNamespaceCtor =
             ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
              _meNamespaceCtor
              {-# LINE 9010 "src/KnotSpec/AG.hs" #-}
              )
         _tsSortDeclsOmeNamespaceNameRoots =
             ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
              _meNamespaceNameRoots
              {-# LINE 9015 "src/KnotSpec/AG.hs" #-}
              )
         _tsSortDeclsOmeNamespaceTypeName =
             ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
              _meNamespaceTypeName
              {-# LINE 9020 "src/KnotSpec/AG.hs" #-}
              )
         _tsSortDeclsOmeRelationEnv =
             ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
              _meRelationEnv
              {-# LINE 9025 "src/KnotSpec/AG.hs" #-}
              )
         _tsSortDeclsOmeSortNameRoots =
             ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
              _meSortNameRoots
              {-# LINE 9030 "src/KnotSpec/AG.hs" #-}
              )
         _tsSortDeclsOmeSortTypeName =
             ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
              _meSortTypeName
              {-# LINE 9035 "src/KnotSpec/AG.hs" #-}
              )
         _tsFunDeclsOmeEnvNameRoots =
             ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
              _meEnvNameRoots
              {-# LINE 9040 "src/KnotSpec/AG.hs" #-}
              )
         _tsFunDeclsOmeEnvTypeName =
             ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
              _meEnvTypeName
              {-# LINE 9045 "src/KnotSpec/AG.hs" #-}
              )
         _tsFunDeclsOmeFunType =
             ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
              _meFunType
              {-# LINE 9050 "src/KnotSpec/AG.hs" #-}
              )
         _tsFunDeclsOmeNamespaceCtor =
             ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
              _meNamespaceCtor
              {-# LINE 9055 "src/KnotSpec/AG.hs" #-}
              )
         _tsFunDeclsOmeNamespaceNameRoots =
             ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
              _meNamespaceNameRoots
              {-# LINE 9060 "src/KnotSpec/AG.hs" #-}
              )
         _tsFunDeclsOmeNamespaceTypeName =
             ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
              _meNamespaceTypeName
              {-# LINE 9065 "src/KnotSpec/AG.hs" #-}
              )
         _tsFunDeclsOmeRelationEnv =
             ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
              _meRelationEnv
              {-# LINE 9070 "src/KnotSpec/AG.hs" #-}
              )
         _tsFunDeclsOmeSortNameRoots =
             ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
              _meSortNameRoots
              {-# LINE 9075 "src/KnotSpec/AG.hs" #-}
              )
         _tsFunDeclsOmeSortTypeName =
             ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
              _meSortTypeName
              {-# LINE 9080 "src/KnotSpec/AG.hs" #-}
              )
         _tsEnvDeclsOmeEnvNameRoots =
             ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
              _meEnvNameRoots
              {-# LINE 9085 "src/KnotSpec/AG.hs" #-}
              )
         _tsEnvDeclsOmeEnvTypeName =
             ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
              _meEnvTypeName
              {-# LINE 9090 "src/KnotSpec/AG.hs" #-}
              )
         _tsEnvDeclsOmeFunType =
             ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
              _meFunType
              {-# LINE 9095 "src/KnotSpec/AG.hs" #-}
              )
         _tsEnvDeclsOmeNamespaceCtor =
             ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
              _meNamespaceCtor
              {-# LINE 9100 "src/KnotSpec/AG.hs" #-}
              )
         _tsEnvDeclsOmeNamespaceNameRoots =
             ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
              _meNamespaceNameRoots
              {-# LINE 9105 "src/KnotSpec/AG.hs" #-}
              )
         _tsEnvDeclsOmeNamespaceTypeName =
             ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
              _meNamespaceTypeName
              {-# LINE 9110 "src/KnotSpec/AG.hs" #-}
              )
         _tsEnvDeclsOmeRelationEnv =
             ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
              _meRelationEnv
              {-# LINE 9115 "src/KnotSpec/AG.hs" #-}
              )
         _tsEnvDeclsOmeSortNameRoots =
             ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
              _meSortNameRoots
              {-# LINE 9120 "src/KnotSpec/AG.hs" #-}
              )
         _tsEnvDeclsOmeSortTypeName =
             ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
              _meSortTypeName
              {-# LINE 9125 "src/KnotSpec/AG.hs" #-}
              )
         _tsRelDeclsOmeEnvNameRoots =
             ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
              _meEnvNameRoots
              {-# LINE 9130 "src/KnotSpec/AG.hs" #-}
              )
         _tsRelDeclsOmeEnvTypeName =
             ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
              _meEnvTypeName
              {-# LINE 9135 "src/KnotSpec/AG.hs" #-}
              )
         _tsRelDeclsOmeFunType =
             ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
              _meFunType
              {-# LINE 9140 "src/KnotSpec/AG.hs" #-}
              )
         _tsRelDeclsOmeNamespaceCtor =
             ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
              _meNamespaceCtor
              {-# LINE 9145 "src/KnotSpec/AG.hs" #-}
              )
         _tsRelDeclsOmeNamespaceNameRoots =
             ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
              _meNamespaceNameRoots
              {-# LINE 9150 "src/KnotSpec/AG.hs" #-}
              )
         _tsRelDeclsOmeNamespaceTypeName =
             ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
              _meNamespaceTypeName
              {-# LINE 9155 "src/KnotSpec/AG.hs" #-}
              )
         _tsRelDeclsOmeRelationEnv =
             ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
              _meRelationEnv
              {-# LINE 9160 "src/KnotSpec/AG.hs" #-}
              )
         _tsRelDeclsOmeSortNameRoots =
             ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
              _meSortNameRoots
              {-# LINE 9165 "src/KnotSpec/AG.hs" #-}
              )
         _tsRelDeclsOmeSortTypeName =
             ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
              _meSortTypeName
              {-# LINE 9170 "src/KnotSpec/AG.hs" #-}
              )
         ( _tsNamespaceDeclsIdesugared,_tsNamespaceDeclsIself,_tsNamespaceDeclsIsmeNamespaceNameRoots) =
             tsNamespaceDecls_ _tsNamespaceDeclsOmeEnvNameRoots _tsNamespaceDeclsOmeEnvTypeName _tsNamespaceDeclsOmeFunType _tsNamespaceDeclsOmeNamespaceCtor _tsNamespaceDeclsOmeNamespaceNameRoots _tsNamespaceDeclsOmeNamespaceTypeName _tsNamespaceDeclsOmeRelationEnv _tsNamespaceDeclsOmeSortNameRoots _tsNamespaceDeclsOmeSortTypeName
         ( _tsSortDeclsIdependencyGraph,_tsSortDeclsIsFunctionDef,_tsSortDeclsIself,_tsSortDeclsIsmeNamespaceCtor,_tsSortDeclsIsmeSortNameRoots,_tsSortDeclsIsmeSortTypeName) =
             tsSortDecls_ _tsSortDeclsOmeEnvNameRoots _tsSortDeclsOmeEnvTypeName _tsSortDeclsOmeFunType _tsSortDeclsOmeNamespaceCtor _tsSortDeclsOmeNamespaceNameRoots _tsSortDeclsOmeNamespaceTypeName _tsSortDeclsOmeRelationEnv _tsSortDeclsOmeSortNameRoots _tsSortDeclsOmeSortTypeName
         ( _tsFunDeclsIdesugared,_tsFunDeclsIsFunctionDef,_tsFunDeclsIself,_tsFunDeclsIsmeFunType) =
             tsFunDecls_ _tsFunDeclsOmeEnvNameRoots _tsFunDeclsOmeEnvTypeName _tsFunDeclsOmeFunType _tsFunDeclsOmeNamespaceCtor _tsFunDeclsOmeNamespaceNameRoots _tsFunDeclsOmeNamespaceTypeName _tsFunDeclsOmeRelationEnv _tsFunDeclsOmeSortNameRoots _tsFunDeclsOmeSortTypeName
         ( _tsEnvDeclsIdesugared,_tsEnvDeclsIself,_tsEnvDeclsIsmeEnvNameRoots) =
             tsEnvDecls_ _tsEnvDeclsOmeEnvNameRoots _tsEnvDeclsOmeEnvTypeName _tsEnvDeclsOmeFunType _tsEnvDeclsOmeNamespaceCtor _tsEnvDeclsOmeNamespaceNameRoots _tsEnvDeclsOmeNamespaceTypeName _tsEnvDeclsOmeRelationEnv _tsEnvDeclsOmeSortNameRoots _tsEnvDeclsOmeSortTypeName
         ( _tsRelDeclsIdesugared,_tsRelDeclsIself,_tsRelDeclsIsmeRelationEnv) =
             tsRelDecls_ _tsRelDeclsOmeEnvNameRoots _tsRelDeclsOmeEnvTypeName _tsRelDeclsOmeFunType _tsRelDeclsOmeNamespaceCtor _tsRelDeclsOmeNamespaceNameRoots _tsRelDeclsOmeNamespaceTypeName _tsRelDeclsOmeRelationEnv _tsRelDeclsOmeSortNameRoots _tsRelDeclsOmeSortTypeName
     in  ( _lhsOdesugared,_lhsOmetaEnvironments,_lhsOself))
-- TypeName ----------------------------------------------------
-- cata
sem_TypeName :: TypeName ->
                T_TypeName
sem_TypeName (TN _tn) =
    (sem_TypeName_TN _tn)
-- semantic domain
type T_TypeName = MEEnvNameRoots ->
                  MEEnvTypeName ->
                  MEFunType ->
                  MENamespaceCtor ->
                  MENamespaceNameRoots ->
                  MENamespaceTypeName ->
                  MERelationEnv ->
                  MESortNameRoots ->
                  MESortTypeName ->
                  ( String,(TcM Core.NamespaceTypeName),(TcM Core.RelationTypeName),TypeName,(TcM Core.SortTypeName))
data Inh_TypeName = Inh_TypeName {meEnvNameRoots_Inh_TypeName :: MEEnvNameRoots,meEnvTypeName_Inh_TypeName :: MEEnvTypeName,meFunType_Inh_TypeName :: MEFunType,meNamespaceCtor_Inh_TypeName :: MENamespaceCtor,meNamespaceNameRoots_Inh_TypeName :: MENamespaceNameRoots,meNamespaceTypeName_Inh_TypeName :: MENamespaceTypeName,meRelationEnv_Inh_TypeName :: MERelationEnv,meSortNameRoots_Inh_TypeName :: MESortNameRoots,meSortTypeName_Inh_TypeName :: MESortTypeName}
data Syn_TypeName = Syn_TypeName {fromTn_Syn_TypeName :: String,namespaceTypeName_Syn_TypeName :: (TcM Core.NamespaceTypeName),relationTypeName_Syn_TypeName :: (TcM Core.RelationTypeName),self_Syn_TypeName :: TypeName,sortTypeName_Syn_TypeName :: (TcM Core.SortTypeName)}
wrap_TypeName :: T_TypeName ->
                 Inh_TypeName ->
                 Syn_TypeName
wrap_TypeName sem (Inh_TypeName _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName) =
    (let ( _lhsOfromTn,_lhsOnamespaceTypeName,_lhsOrelationTypeName,_lhsOself,_lhsOsortTypeName) = sem _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName
     in  (Syn_TypeName _lhsOfromTn _lhsOnamespaceTypeName _lhsOrelationTypeName _lhsOself _lhsOsortTypeName))
sem_TypeName_TN :: String ->
                   T_TypeName
sem_TypeName_TN tn_ =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOsortTypeName :: (TcM Core.SortTypeName)
              _lhsOnamespaceTypeName :: (TcM Core.NamespaceTypeName)
              _lhsOrelationTypeName :: (TcM Core.RelationTypeName)
              _lhsOfromTn :: String
              _lhsOself :: TypeName
              _lhsOsortTypeName =
                  ({-# LINE 156 "src/KnotSpec/Desugaring.ag" #-}
                   case Data.Map.lookup _self     _lhsImeSortNameRoots of
                     Just _  -> return (Core.STN tn_)
                     Nothing -> throwError $ "Cannot find sort typename of " ++ tn_
                   {-# LINE 9230 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOnamespaceTypeName =
                  ({-# LINE 160 "src/KnotSpec/Desugaring.ag" #-}
                   case Data.Map.lookup _self     _lhsImeNamespaceNameRoots of
                     Just _  -> return (Core.NTN tn_)
                     Nothing -> throwError $ "Cannot find namespace typename of " ++ tn_
                   {-# LINE 9237 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOrelationTypeName =
                  ({-# LINE 164 "src/KnotSpec/Desugaring.ag" #-}
                   return (Core.RTN tn_)
                   {-# LINE 9242 "src/KnotSpec/AG.hs" #-}
                   )
              _lhsOfromTn =
                  ({-# LINE 165 "src/KnotSpec/Desugaring.ag" #-}
                   tn_
                   {-# LINE 9247 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  TN tn_
              _lhsOself =
                  _self
          in  ( _lhsOfromTn,_lhsOnamespaceTypeName,_lhsOrelationTypeName,_lhsOself,_lhsOsortTypeName)))
-- TypeNames ---------------------------------------------------
-- cata
sem_TypeNames :: TypeNames ->
                 T_TypeNames
sem_TypeNames list =
    (Prelude.foldr sem_TypeNames_Cons sem_TypeNames_Nil (Prelude.map sem_TypeName list))
-- semantic domain
type T_TypeNames = MEEnvNameRoots ->
                   MEEnvTypeName ->
                   MEFunType ->
                   MENamespaceCtor ->
                   MENamespaceNameRoots ->
                   MENamespaceTypeName ->
                   MERelationEnv ->
                   MESortNameRoots ->
                   MESortTypeName ->
                   ( (TcM [Core.NamespaceTypeName]),TypeNames)
data Inh_TypeNames = Inh_TypeNames {meEnvNameRoots_Inh_TypeNames :: MEEnvNameRoots,meEnvTypeName_Inh_TypeNames :: MEEnvTypeName,meFunType_Inh_TypeNames :: MEFunType,meNamespaceCtor_Inh_TypeNames :: MENamespaceCtor,meNamespaceNameRoots_Inh_TypeNames :: MENamespaceNameRoots,meNamespaceTypeName_Inh_TypeNames :: MENamespaceTypeName,meRelationEnv_Inh_TypeNames :: MERelationEnv,meSortNameRoots_Inh_TypeNames :: MESortNameRoots,meSortTypeName_Inh_TypeNames :: MESortTypeName}
data Syn_TypeNames = Syn_TypeNames {namespaceTypeName_Syn_TypeNames :: (TcM [Core.NamespaceTypeName]),self_Syn_TypeNames :: TypeNames}
wrap_TypeNames :: T_TypeNames ->
                  Inh_TypeNames ->
                  Syn_TypeNames
wrap_TypeNames sem (Inh_TypeNames _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName) =
    (let ( _lhsOnamespaceTypeName,_lhsOself) = sem _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName
     in  (Syn_TypeNames _lhsOnamespaceTypeName _lhsOself))
sem_TypeNames_Cons :: T_TypeName ->
                      T_TypeNames ->
                      T_TypeNames
sem_TypeNames_Cons hd_ tl_ =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOnamespaceTypeName :: (TcM [Core.NamespaceTypeName])
              _lhsOself :: TypeNames
              _hdOmeEnvNameRoots :: MEEnvNameRoots
              _hdOmeEnvTypeName :: MEEnvTypeName
              _hdOmeFunType :: MEFunType
              _hdOmeNamespaceCtor :: MENamespaceCtor
              _hdOmeNamespaceNameRoots :: MENamespaceNameRoots
              _hdOmeNamespaceTypeName :: MENamespaceTypeName
              _hdOmeRelationEnv :: MERelationEnv
              _hdOmeSortNameRoots :: MESortNameRoots
              _hdOmeSortTypeName :: MESortTypeName
              _tlOmeEnvNameRoots :: MEEnvNameRoots
              _tlOmeEnvTypeName :: MEEnvTypeName
              _tlOmeFunType :: MEFunType
              _tlOmeNamespaceCtor :: MENamespaceCtor
              _tlOmeNamespaceNameRoots :: MENamespaceNameRoots
              _tlOmeNamespaceTypeName :: MENamespaceTypeName
              _tlOmeRelationEnv :: MERelationEnv
              _tlOmeSortNameRoots :: MESortNameRoots
              _tlOmeSortTypeName :: MESortTypeName
              _hdIfromTn :: String
              _hdInamespaceTypeName :: (TcM Core.NamespaceTypeName)
              _hdIrelationTypeName :: (TcM Core.RelationTypeName)
              _hdIself :: TypeName
              _hdIsortTypeName :: (TcM Core.SortTypeName)
              _tlInamespaceTypeName :: (TcM [Core.NamespaceTypeName])
              _tlIself :: TypeNames
              _lhsOnamespaceTypeName =
                  ({-# LINE 152 "src/KnotSpec/Desugaring.ag" #-}
                   (consA _hdInamespaceTypeName _tlInamespaceTypeName)
                   {-# LINE 9322 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _hdOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 9331 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 9336 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 9341 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 9346 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 9351 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 9356 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 9361 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 9366 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 9371 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 9376 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 9381 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 9386 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 9391 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 9396 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 9401 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 9406 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 9411 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 9416 "src/KnotSpec/AG.hs" #-}
                   )
              ( _hdIfromTn,_hdInamespaceTypeName,_hdIrelationTypeName,_hdIself,_hdIsortTypeName) =
                  hd_ _hdOmeEnvNameRoots _hdOmeEnvTypeName _hdOmeFunType _hdOmeNamespaceCtor _hdOmeNamespaceNameRoots _hdOmeNamespaceTypeName _hdOmeRelationEnv _hdOmeSortNameRoots _hdOmeSortTypeName
              ( _tlInamespaceTypeName,_tlIself) =
                  tl_ _tlOmeEnvNameRoots _tlOmeEnvTypeName _tlOmeFunType _tlOmeNamespaceCtor _tlOmeNamespaceNameRoots _tlOmeNamespaceTypeName _tlOmeRelationEnv _tlOmeSortNameRoots _tlOmeSortTypeName
          in  ( _lhsOnamespaceTypeName,_lhsOself)))
sem_TypeNames_Nil :: T_TypeNames
sem_TypeNames_Nil =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOnamespaceTypeName :: (TcM [Core.NamespaceTypeName])
              _lhsOself :: TypeNames
              _lhsOnamespaceTypeName =
                  ({-# LINE 152 "src/KnotSpec/Desugaring.ag" #-}
                   memptyA
                   {-# LINE 9439 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  []
              _lhsOself =
                  _self
          in  ( _lhsOnamespaceTypeName,_lhsOself)))
-- Vle ---------------------------------------------------------
-- cata
sem_Vle :: Vle ->
           T_Vle
sem_Vle list =
    (Prelude.foldr sem_Vle_Cons sem_Vle_Nil (Prelude.map sem_VleItem list))
-- semantic domain
type T_Vle = MEEnvNameRoots ->
             MEEnvTypeName ->
             MEFunType ->
             MENamespaceCtor ->
             MENamespaceNameRoots ->
             MENamespaceTypeName ->
             MERelationEnv ->
             MESortNameRoots ->
             MESortTypeName ->
             ( (TcM Core.Vle),Vle)
data Inh_Vle = Inh_Vle {meEnvNameRoots_Inh_Vle :: MEEnvNameRoots,meEnvTypeName_Inh_Vle :: MEEnvTypeName,meFunType_Inh_Vle :: MEFunType,meNamespaceCtor_Inh_Vle :: MENamespaceCtor,meNamespaceNameRoots_Inh_Vle :: MENamespaceNameRoots,meNamespaceTypeName_Inh_Vle :: MENamespaceTypeName,meRelationEnv_Inh_Vle :: MERelationEnv,meSortNameRoots_Inh_Vle :: MESortNameRoots,meSortTypeName_Inh_Vle :: MESortTypeName}
data Syn_Vle = Syn_Vle {desugared_Syn_Vle :: (TcM Core.Vle),self_Syn_Vle :: Vle}
wrap_Vle :: T_Vle ->
            Inh_Vle ->
            Syn_Vle
wrap_Vle sem (Inh_Vle _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName) =
    (let ( _lhsOdesugared,_lhsOself) = sem _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName
     in  (Syn_Vle _lhsOdesugared _lhsOself))
sem_Vle_Cons :: T_VleItem ->
                T_Vle ->
                T_Vle
sem_Vle_Cons hd_ tl_ =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOdesugared :: (TcM Core.Vle)
              _lhsOself :: Vle
              _hdOmeEnvNameRoots :: MEEnvNameRoots
              _hdOmeEnvTypeName :: MEEnvTypeName
              _hdOmeFunType :: MEFunType
              _hdOmeNamespaceCtor :: MENamespaceCtor
              _hdOmeNamespaceNameRoots :: MENamespaceNameRoots
              _hdOmeNamespaceTypeName :: MENamespaceTypeName
              _hdOmeRelationEnv :: MERelationEnv
              _hdOmeSortNameRoots :: MESortNameRoots
              _hdOmeSortTypeName :: MESortTypeName
              _tlOmeEnvNameRoots :: MEEnvNameRoots
              _tlOmeEnvTypeName :: MEEnvTypeName
              _tlOmeFunType :: MEFunType
              _tlOmeNamespaceCtor :: MENamespaceCtor
              _tlOmeNamespaceNameRoots :: MENamespaceNameRoots
              _tlOmeNamespaceTypeName :: MENamespaceTypeName
              _tlOmeRelationEnv :: MERelationEnv
              _tlOmeSortNameRoots :: MESortNameRoots
              _tlOmeSortTypeName :: MESortTypeName
              _hdIdesugared :: (TcM Core.VleItem)
              _hdIself :: VleItem
              _tlIdesugared :: (TcM Core.Vle)
              _tlIself :: Vle
              _lhsOdesugared =
                  ({-# LINE 181 "src/KnotSpec/Desugaring.ag" #-}
                   (consA _hdIdesugared _tlIdesugared)
                   {-# LINE 9511 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _hdOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 9520 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 9525 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 9530 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 9535 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 9540 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 9545 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 9550 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 9555 "src/KnotSpec/AG.hs" #-}
                   )
              _hdOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 9560 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 9565 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 9570 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 9575 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 9580 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 9585 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 9590 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 9595 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 9600 "src/KnotSpec/AG.hs" #-}
                   )
              _tlOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 9605 "src/KnotSpec/AG.hs" #-}
                   )
              ( _hdIdesugared,_hdIself) =
                  hd_ _hdOmeEnvNameRoots _hdOmeEnvTypeName _hdOmeFunType _hdOmeNamespaceCtor _hdOmeNamespaceNameRoots _hdOmeNamespaceTypeName _hdOmeRelationEnv _hdOmeSortNameRoots _hdOmeSortTypeName
              ( _tlIdesugared,_tlIself) =
                  tl_ _tlOmeEnvNameRoots _tlOmeEnvTypeName _tlOmeFunType _tlOmeNamespaceCtor _tlOmeNamespaceNameRoots _tlOmeNamespaceTypeName _tlOmeRelationEnv _tlOmeSortNameRoots _tlOmeSortTypeName
          in  ( _lhsOdesugared,_lhsOself)))
sem_Vle_Nil :: T_Vle
sem_Vle_Nil =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOdesugared :: (TcM Core.Vle)
              _lhsOself :: Vle
              _lhsOdesugared =
                  ({-# LINE 181 "src/KnotSpec/Desugaring.ag" #-}
                   memptyA
                   {-# LINE 9628 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  []
              _lhsOself =
                  _self
          in  ( _lhsOdesugared,_lhsOself)))
-- VleItem -----------------------------------------------------
-- cata
sem_VleItem :: VleItem ->
               T_VleItem
sem_VleItem (VleBinding _vleMetavar) =
    (sem_VleItem_VleBinding (sem_Name _vleMetavar))
sem_VleItem (VleCall _vleFunName _vleField) =
    (sem_VleItem_VleCall _vleFunName (sem_Name _vleField))
-- semantic domain
type T_VleItem = MEEnvNameRoots ->
                 MEEnvTypeName ->
                 MEFunType ->
                 MENamespaceCtor ->
                 MENamespaceNameRoots ->
                 MENamespaceTypeName ->
                 MERelationEnv ->
                 MESortNameRoots ->
                 MESortTypeName ->
                 ( (TcM Core.VleItem),VleItem)
data Inh_VleItem = Inh_VleItem {meEnvNameRoots_Inh_VleItem :: MEEnvNameRoots,meEnvTypeName_Inh_VleItem :: MEEnvTypeName,meFunType_Inh_VleItem :: MEFunType,meNamespaceCtor_Inh_VleItem :: MENamespaceCtor,meNamespaceNameRoots_Inh_VleItem :: MENamespaceNameRoots,meNamespaceTypeName_Inh_VleItem :: MENamespaceTypeName,meRelationEnv_Inh_VleItem :: MERelationEnv,meSortNameRoots_Inh_VleItem :: MESortNameRoots,meSortTypeName_Inh_VleItem :: MESortTypeName}
data Syn_VleItem = Syn_VleItem {desugared_Syn_VleItem :: (TcM Core.VleItem),self_Syn_VleItem :: VleItem}
wrap_VleItem :: T_VleItem ->
                Inh_VleItem ->
                Syn_VleItem
wrap_VleItem sem (Inh_VleItem _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName) =
    (let ( _lhsOdesugared,_lhsOself) = sem _lhsImeEnvNameRoots _lhsImeEnvTypeName _lhsImeFunType _lhsImeNamespaceCtor _lhsImeNamespaceNameRoots _lhsImeNamespaceTypeName _lhsImeRelationEnv _lhsImeSortNameRoots _lhsImeSortTypeName
     in  (Syn_VleItem _lhsOdesugared _lhsOself))
sem_VleItem_VleBinding :: T_Name ->
                          T_VleItem
sem_VleItem_VleBinding vleMetavar_ =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOself :: VleItem
              _lhsOdesugared :: (TcM Core.VleItem)
              _vleMetavarOmeEnvNameRoots :: MEEnvNameRoots
              _vleMetavarOmeEnvTypeName :: MEEnvTypeName
              _vleMetavarOmeFunType :: MEFunType
              _vleMetavarOmeNamespaceCtor :: MENamespaceCtor
              _vleMetavarOmeNamespaceNameRoots :: MENamespaceNameRoots
              _vleMetavarOmeNamespaceTypeName :: MENamespaceTypeName
              _vleMetavarOmeRelationEnv :: MERelationEnv
              _vleMetavarOmeSortNameRoots :: MESortNameRoots
              _vleMetavarOmeSortTypeName :: MESortTypeName
              _vleMetavarIcoreFieldName :: (TcM CoreFieldName)
              _vleMetavarIcoreTypeName :: (TcM CoreTypeName)
              _vleMetavarIfieldMetaBinding :: (TcM Core.FieldMetaBinding)
              _vleMetavarImetavarName :: (TcM Core.MetavarVar)
              _vleMetavarInamespaceTypeName :: (TcM Core.NamespaceTypeName)
              _vleMetavarIroot :: NameRoot
              _vleMetavarIself :: Name
              _vleMetavarIsubtreeName :: (TcM Core.SubtreeVar)
              _vleMetavarIsuffix :: String
              _desugared =
                  ({-# LINE 300 "src/KnotSpec/Desugaring.ag" #-}
                   Core.VleBinding
                     <$> sequence [_vleMetavarInamespaceTypeName]
                     <*> _vleMetavarImetavarName
                   {-# LINE 9699 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  VleBinding _vleMetavarIself
              _lhsOself =
                  _self
              _lhsOdesugared =
                  ({-# LINE 182 "src/KnotSpec/Desugaring.ag" #-}
                   _desugared
                   {-# LINE 9708 "src/KnotSpec/AG.hs" #-}
                   )
              _vleMetavarOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 9713 "src/KnotSpec/AG.hs" #-}
                   )
              _vleMetavarOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 9718 "src/KnotSpec/AG.hs" #-}
                   )
              _vleMetavarOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 9723 "src/KnotSpec/AG.hs" #-}
                   )
              _vleMetavarOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 9728 "src/KnotSpec/AG.hs" #-}
                   )
              _vleMetavarOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 9733 "src/KnotSpec/AG.hs" #-}
                   )
              _vleMetavarOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 9738 "src/KnotSpec/AG.hs" #-}
                   )
              _vleMetavarOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 9743 "src/KnotSpec/AG.hs" #-}
                   )
              _vleMetavarOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 9748 "src/KnotSpec/AG.hs" #-}
                   )
              _vleMetavarOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 9753 "src/KnotSpec/AG.hs" #-}
                   )
              ( _vleMetavarIcoreFieldName,_vleMetavarIcoreTypeName,_vleMetavarIfieldMetaBinding,_vleMetavarImetavarName,_vleMetavarInamespaceTypeName,_vleMetavarIroot,_vleMetavarIself,_vleMetavarIsubtreeName,_vleMetavarIsuffix) =
                  vleMetavar_ _vleMetavarOmeEnvNameRoots _vleMetavarOmeEnvTypeName _vleMetavarOmeFunType _vleMetavarOmeNamespaceCtor _vleMetavarOmeNamespaceNameRoots _vleMetavarOmeNamespaceTypeName _vleMetavarOmeRelationEnv _vleMetavarOmeSortNameRoots _vleMetavarOmeSortTypeName
          in  ( _lhsOdesugared,_lhsOself)))
sem_VleItem_VleCall :: FunName ->
                       T_Name ->
                       T_VleItem
sem_VleItem_VleCall vleFunName_ vleField_ =
    (\ _lhsImeEnvNameRoots
       _lhsImeEnvTypeName
       _lhsImeFunType
       _lhsImeNamespaceCtor
       _lhsImeNamespaceNameRoots
       _lhsImeNamespaceTypeName
       _lhsImeRelationEnv
       _lhsImeSortNameRoots
       _lhsImeSortTypeName ->
         (let _lhsOself :: VleItem
              _lhsOdesugared :: (TcM Core.VleItem)
              _vleFieldOmeEnvNameRoots :: MEEnvNameRoots
              _vleFieldOmeEnvTypeName :: MEEnvTypeName
              _vleFieldOmeFunType :: MEFunType
              _vleFieldOmeNamespaceCtor :: MENamespaceCtor
              _vleFieldOmeNamespaceNameRoots :: MENamespaceNameRoots
              _vleFieldOmeNamespaceTypeName :: MENamespaceTypeName
              _vleFieldOmeRelationEnv :: MERelationEnv
              _vleFieldOmeSortNameRoots :: MESortNameRoots
              _vleFieldOmeSortTypeName :: MESortTypeName
              _vleFieldIcoreFieldName :: (TcM CoreFieldName)
              _vleFieldIcoreTypeName :: (TcM CoreTypeName)
              _vleFieldIfieldMetaBinding :: (TcM Core.FieldMetaBinding)
              _vleFieldImetavarName :: (TcM Core.MetavarVar)
              _vleFieldInamespaceTypeName :: (TcM Core.NamespaceTypeName)
              _vleFieldIroot :: NameRoot
              _vleFieldIself :: Name
              _vleFieldIsubtreeName :: (TcM Core.SubtreeVar)
              _vleFieldIsuffix :: String
              _desugared =
                  ({-# LINE 295 "src/KnotSpec/Desugaring.ag" #-}
                   do
                    (stn,ntns) <- lookupFunType vleFunName_ _lhsImeFunType
                    Core.VleCall ntns (Core.FN vleFunName_ stn ntns) <$> _vleFieldIsubtreeName
                   {-# LINE 9796 "src/KnotSpec/AG.hs" #-}
                   )
              _self =
                  VleCall vleFunName_ _vleFieldIself
              _lhsOself =
                  _self
              _lhsOdesugared =
                  ({-# LINE 182 "src/KnotSpec/Desugaring.ag" #-}
                   _desugared
                   {-# LINE 9805 "src/KnotSpec/AG.hs" #-}
                   )
              _vleFieldOmeEnvNameRoots =
                  ({-# LINE 200 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvNameRoots
                   {-# LINE 9810 "src/KnotSpec/AG.hs" #-}
                   )
              _vleFieldOmeEnvTypeName =
                  ({-# LINE 201 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeEnvTypeName
                   {-# LINE 9815 "src/KnotSpec/AG.hs" #-}
                   )
              _vleFieldOmeFunType =
                  ({-# LINE 178 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeFunType
                   {-# LINE 9820 "src/KnotSpec/AG.hs" #-}
                   )
              _vleFieldOmeNamespaceCtor =
                  ({-# LINE 148 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceCtor
                   {-# LINE 9825 "src/KnotSpec/AG.hs" #-}
                   )
              _vleFieldOmeNamespaceNameRoots =
                  ({-# LINE 78 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceNameRoots
                   {-# LINE 9830 "src/KnotSpec/AG.hs" #-}
                   )
              _vleFieldOmeNamespaceTypeName =
                  ({-# LINE 79 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeNamespaceTypeName
                   {-# LINE 9835 "src/KnotSpec/AG.hs" #-}
                   )
              _vleFieldOmeRelationEnv =
                  ({-# LINE 235 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeRelationEnv
                   {-# LINE 9840 "src/KnotSpec/AG.hs" #-}
                   )
              _vleFieldOmeSortNameRoots =
                  ({-# LINE 107 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortNameRoots
                   {-# LINE 9845 "src/KnotSpec/AG.hs" #-}
                   )
              _vleFieldOmeSortTypeName =
                  ({-# LINE 108 "src/KnotSpec/Environment.ag" #-}
                   _lhsImeSortTypeName
                   {-# LINE 9850 "src/KnotSpec/AG.hs" #-}
                   )
              ( _vleFieldIcoreFieldName,_vleFieldIcoreTypeName,_vleFieldIfieldMetaBinding,_vleFieldImetavarName,_vleFieldInamespaceTypeName,_vleFieldIroot,_vleFieldIself,_vleFieldIsubtreeName,_vleFieldIsuffix) =
                  vleField_ _vleFieldOmeEnvNameRoots _vleFieldOmeEnvTypeName _vleFieldOmeFunType _vleFieldOmeNamespaceCtor _vleFieldOmeNamespaceNameRoots _vleFieldOmeNamespaceTypeName _vleFieldOmeRelationEnv _vleFieldOmeSortNameRoots _vleFieldOmeSortTypeName
          in  ( _lhsOdesugared,_lhsOself)))