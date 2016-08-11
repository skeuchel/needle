{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}

module KnotSpec.Group where

import           KnotSpec.Syntax
import           KnotSpec.Environment

import           Control.Arrow
import qualified Data.Foldable as F
import           Data.Graph (flattenSCC, stronglyConnComp)
import           Data.List (nub, sort)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Maybe (catMaybes)
import           Data.Set (Set)
import qualified Data.Set as S

-- This defines a node 'SortName' in the graph with
-- label 'DN' and adjacent nodes 'SortNames'.
type DepNode = (DN, SortTypeName, [SortTypeName])

-- The label includes the desugared SortDecl, the sort and
-- namespace dependencies.
type DN  = (SortDecl 'Grouped, Set SortTypeName, Set NamespaceTypeName)

-- A strongly connected component with combined labels.
type DNG =
  ([SortDecl 'Grouped],
   Set SortTypeName,
   Set NamespaceTypeName
  )

namespaceDependencies :: [CtorDecl 'Checked] -> Set NamespaceTypeName
namespaceDependencies = S.unions . map ctorDecl
  where
    ctorDecl :: CtorDecl 'Checked -> Set NamespaceTypeName
    ctorDecl (CtorVar _ rv)  = S.singleton $ fvNtn rv
    ctorDecl (CtorReg _ fds) = S.unions $ map fieldDecl fds

    fieldDecl :: FieldDecl w 'Checked 'Checked -> Set NamespaceTypeName
    fieldDecl (FieldDeclSort{})         = S.empty
    fieldDecl (FieldDeclEnv{})          = S.empty
    fieldDecl (FieldDeclSet{})          = S.empty
    fieldDecl (FieldDeclBinding{})      = S.empty
    fieldDecl (FieldDeclReference _ rv) = S.singleton $ fvNtn rv


sortDependencies :: [CtorDecl 'Checked] -> Set SortTypeName
sortDependencies = S.unions . map ctorDecl
  where
    ctorDecl :: CtorDecl 'Checked -> Set SortTypeName
    ctorDecl (CtorVar{})     = S.empty
    ctorDecl (CtorReg _ fds) = S.unions $ map fieldDecl fds

    fieldDecl :: FieldDecl w 'Checked 'Checked -> Set SortTypeName
    fieldDecl (FieldDeclSort _ _ sv) = S.singleton $ svStn sv
    fieldDecl (FieldDeclEnv{})       = S.empty -- TODO: Should be desugared
    fieldDecl (FieldDeclBinding{})   = S.empty
    fieldDecl (FieldDeclSet{})       = S.empty
    fieldDecl (FieldDeclReference{}) = S.empty

checked2grouped :: [CtorDecl 'Checked] -> [CtorDecl 'Grouped]
checked2grouped = map ctorDecl
  where
    ctorDecl :: CtorDecl 'Checked -> CtorDecl 'Grouped
    ctorDecl (CtorVar cn rv)  = CtorVar cn rv
    ctorDecl (CtorReg cn fds) = CtorReg cn (map fieldDecl fds)

fieldDecl :: FieldDecl w 'Checked 'Checked -> FieldDecl w 'Grouped 'Grouped
fieldDecl (FieldDeclSort loc bs sv)    = FieldDeclSort loc (bindSpec bs) sv
fieldDecl (FieldDeclEnv loc bs ev)     = FieldDeclEnv loc (bindSpec bs) ev
fieldDecl (FieldDeclBinding loc bs bv) = FieldDeclBinding loc (bindSpec bs) bv
fieldDecl (FieldDeclReference loc rv)  = FieldDeclReference loc rv
fieldDecl (FieldDeclSet loc zv)        = FieldDeclSet loc zv

bindSpec :: BindSpec 'Checked -> BindSpec 'Grouped
bindSpec = fmap bindSpecItem

bindSpecItem :: BindSpecItem 'Checked -> BindSpecItem 'Grouped
bindSpecItem (BsiBinding bv) = BsiBinding bv
bindSpecItem (BsiCall fn sv) = BsiCall fn sv

dependencyNode :: SortDecl 'Checked -> DepNode
dependencyNode (SortDecl stn nrs cds) = node
  where
    sortDeps = sortDependencies cds
    label =
      ( SortDecl stn nrs (checked2grouped cds)
      , sortDeps
      , namespaceDependencies cds
      )
    node =
      (label,stn,S.toList sortDeps)

sortDepAnalysis :: [DepNode] -> [DNG]
sortDepAnalysis = map (flattenDNS . flattenSCC) . stronglyConnComp

flattenDNS :: [DN] -> DNG
flattenDNS dns = (sds, S.unions sortDeps, S.unions namespaceDeps)
  where (sds,sortDeps,namespaceDeps) = unzip3 dns


-- This function folds the strongly connected components in topological
-- order. It builds a mapping [SortName -> Set NamespaceName] so that the
-- namespace dependencies for each component can be resolved.
namespaceDepAnalysis' :: [DNG] -> Map SortTypeName (Set NamespaceTypeName) -> [SortGroupDecl 'Grouped]
namespaceDepAnalysis' []                                              _               = []
namespaceDepAnalysis' ((sortDecls,sortNames,namespaceDepDirect):dngs) namespaceDepAcc = res
  where
    -- These are the namespace dependencies we inherit from the sort
    -- dependencies.
    namespaceDepIndirect :: Set NamespaceTypeName
    namespaceDepIndirect = S.unions $ catMaybes
                             [ M.lookup sortName namespaceDepAcc
                             | sortName <- S.toList sortNames
                             ]

    -- The final set is the union of direct and indirect dependencies
    namespaceDepFinal :: Set NamespaceTypeName
    namespaceDepFinal = S.union namespaceDepDirect namespaceDepIndirect

    -- This is the namespace dependency mapping for each sort declaration in
    -- this group.
    namespaceDepAcc' :: Map SortTypeName (Set NamespaceTypeName)
    namespaceDepAcc' = M.fromList
                         [ (sortName,namespaceDepFinal)
                         | (SortDecl sortName _ _) <- sortDecls
                         ]

    -- The group of sort declarations that we construct for the current
    -- component.
    sgtn :: SortGroupTypeName
    sgtn = groupName (map sdTypeName sortDecls)
    hasBindspecs :: Bool
    hasBindspecs = not . null $
                     [ ()
                     | sd <- sortDecls
                     , CtorReg _ fds <- sdCtors sd
                     , FieldDeclSort _ (_:._) _ <- fds
                     ]
    sg :: SortGroupDecl 'Grouped
    sg = SortGroupDecl
           sgtn
           sortDecls
           (S.toList namespaceDepFinal)
           hasBindspecs

    res = sg : namespaceDepAnalysis' dngs (M.union namespaceDepAcc' namespaceDepAcc)

namespaceDepAnalysis :: [DNG] -> [SortGroupDecl 'Grouped]
namespaceDepAnalysis dngs = namespaceDepAnalysis' dngs mempty

dependencyAnalysis :: [DepNode] -> [SortGroupDecl 'Grouped]
dependencyAnalysis = namespaceDepAnalysis . sortDepAnalysis

group :: TermSpec 'Checked -> TermSpec 'Grouped
group (TermSpec nds sds eds fds rds zds) =
  TermSpecGrouped (map namespaceDecl nds) sgds' (map envDecl eds) fgds' rgds' zgds'
  where
    graph :: [DepNode]
    graph = map dependencyNode sds
    sgds' :: [SortGroupDecl 'Grouped]
    sgds' = dependencyAnalysis graph

    fdss' :: [[FunDecl 'Grouped]]
    fdss' = map flattenSCC . stronglyConnComp $ map funDeclToNode fds
    fgds' :: [FunGroupDecl 'Grouped]
    fgds' = map (makeFunGroup (mkMESortGroupOfSort SGrouped sgds')) fdss'

    rdss :: [[RelationDecl 'Grouped]]
    rdss = map flattenSCC . stronglyConnComp $ map relDeclToNode rds
    rgds' :: [RelationGroupDecl 'Grouped]
    rgds' = map RelationGroupDecl rdss

    zdss :: [[SetDecl 'Grouped]]
    zdss = map flattenSCC . stronglyConnComp $ map setDeclToNode zds
    zgds' :: [SetGroupDecl 'Grouped]
    zgds' = map SetGroupDecl zdss

    namespaceDecl :: NamespaceDecl 'Checked -> NamespaceDecl 'Grouped
    namespaceDecl (NamespaceDecl beg ntn nrs mbSort dirs end) =
      NamespaceDecl beg ntn nrs mbSort dirs end

    makeFunGroup :: MESortGroupOfSort 'Grouped -> [FunDecl 'Grouped] -> FunGroupDecl 'Grouped
    makeFunGroup meGroupOf fds' =
        FunGroupDecl
          (funGroupName $ map fdName fds')
          sgtn
          (M.toList fgd')
      where
        fgd' :: Map SortTypeName [FunDecl 'Grouped]
        fgd' = M.fromListWith (++) [ (fdSource fd, [fd]) | fd <- fds' ]
        stn  = fdSource $ head fds
        sgtn = M.findWithDefault (error "makeFunGroup") stn meGroupOf

    funDeclToNode :: FunDecl 'Checked -> (FunDecl 'Grouped, FunName, [FunName])
    funDeclToNode fd = (funDecl fd, fdName fd, nub $ sort fns)
      where fns = [ fn
                  | fc  <- fdCases fd
                  , BsiCall {bsiFunName = fn} <- F.toList (fcRhs fc)
                  ]

    relDeclToNode :: RelationDecl 'Checked ->
      (RelationDecl 'Grouped, RelationTypeName, [RelationTypeName])
    relDeclToNode (RelationDecl mbEtn rtn fields nrs outputs rules) =
      (RelationDecl mbEtn rtn (map fieldDecl fields) nrs outputs (map ruleDecl rules), rtn, rtns)
      where rtns = [ jmtRelationTypeName jm| RuleReg _ _ fml conc _ <- rules
                   , jm <- conc : [ jm | FormJudgement _ _ jm _ <- fml ]
                   ]

    setDeclToNode :: SetDecl 'Checked ->
      (SetDecl 'Grouped, SetTypeName, [SetTypeName])
    setDeclToNode (SetDecl ztn nrs zcs) =
      (SetDecl ztn nrs (map setCtorDecl zcs), ztn, ztns)
      where ztns = [ zvZtn zv
                   | SetCtor _cn zfds <- zcs
                   , SetFieldDecl _loc zv <- zfds
                   ]

    funDecl :: FunDecl 'Checked -> FunDecl 'Grouped
    funDecl (FunDecl fn stn ntns cases) =
      FunDecl fn stn ntns (map funCase cases)

    funCase :: FunCase 'Checked -> FunCase 'Grouped
    funCase (FunCase cn ffds rhs) =
      FunCase cn (map funField ffds) (bindSpec rhs)

    funField :: FunField 'Checked -> FunField 'Grouped
    funField (FunFieldSort sv)      = FunFieldSort sv
    funField (FunFieldReference rv) = FunFieldReference rv
    funField (FunFieldBinding bv)   = FunFieldBinding bv
    funField (FunFieldEnv ev)       = FunFieldEnv ev
    funField (FunFieldSet zv)       = FunFieldSet zv

    bindSpec :: BindSpec 'Checked -> BindSpec 'Grouped
    bindSpec = fmap bindSpecItem

    bindSpecItem :: BindSpecItem 'Checked -> BindSpecItem 'Grouped
    bindSpecItem (BsiBinding bv) = BsiBinding bv
    bindSpecItem (BsiCall fn sv) = BsiCall fn sv

    envDecl :: EnvDecl 'Checked -> EnvDecl 'Grouped
    envDecl (EnvDecl etn nrs ecds) = EnvDecl etn nrs (map envCtorDecl ecds)

    envCtorDecl :: EnvCtorDecl 'Checked -> EnvCtorDecl 'Grouped
    envCtorDecl (EnvCtorNil cn)          = EnvCtorNil cn
    envCtorDecl (EnvCtorCons cn bv efds mbRtn) =
      EnvCtorCons cn bv (map fieldDecl efds) mbRtn

    setCtorDecl :: SetCtorDecl 'Checked -> SetCtorDecl 'Grouped
    setCtorDecl (SetCtor cn zfds) = SetCtor cn (map setFieldDecl zfds)

    setFieldDecl :: SetFieldDecl 'Checked -> SetFieldDecl 'Grouped
    setFieldDecl (SetFieldDecl loc zv) = SetFieldDecl loc zv

    ruleDecl :: Rule 'Checked -> Rule 'Grouped
    ruleDecl r = case r of
      RuleVar cn rmbs etn fv sfs jm -> do
        RuleVar cn
          (map ruleMetavarBinder rmbs)
          etn fv
          (map symbolicField sfs)
          (judgement jm)

      RuleReg cn rmbs fms jm outputs ->
        RuleReg cn
          (map ruleMetavarBinder rmbs)
          (map formula fms)
          (judgement jm)
          (map (second ruleBindSpec) outputs)

    ruleMetavarBinder :: RuleMetavarBinder 'Checked -> RuleMetavarBinder 'Grouped
    ruleMetavarBinder rmb = case rmb of
      RuleMetavarSort bs sv    -> RuleMetavarSort (bindSpec bs) sv
      RuleMetavarBinding bs bv -> RuleMetavarBinding (bindSpec bs) bv
      RuleMetavarFree fv       -> RuleMetavarFree fv
      RuleMetavarSet zv        -> RuleMetavarSet zv

    formula :: Formula 'Checked -> Formula 'Grouped
    formula (FormLookup etn rv sfs) =
      FormLookup etn rv (map symbolicField sfs)
    formula (FormJudgement jmv rbs jm outs) =
      FormJudgement jmv (ruleBindSpec rbs) (judgement jm) outs

    ruleBindSpec :: RuleBindSpec 'Checked -> RuleBindSpec 'Grouped
    ruleBindSpec = fmap ruleBindSpecItem

    ruleBindSpecItem :: RuleBindSpecItem 'Checked -> RuleBindSpecItem 'Grouped
    ruleBindSpecItem (RuleBsiBinding bv sfs) =
      RuleBsiBinding bv (symbolicField <$> sfs)
    ruleBindSpecItem (RuleBsiCall fn jmv) =
      RuleBsiCall fn jmv

    judgement :: Judgement 'Checked -> Judgement 'Grouped
    judgement (Judgement rtn mbEtn sfs) =
      Judgement rtn mbEtn (symbolicField <$> sfs)

    symbolicTerm :: SymbolicTerm 'Checked -> SymbolicTerm 'Grouped
    symbolicTerm st = case st of
      SymVar bs sv               -> SymVar (bindSpec bs) sv
      SymCtorVarFree bs cn rv    -> SymCtorVarFree (bindSpec bs) cn rv
      SymCtorVarBound bs cn rv   -> SymCtorVarBound (bindSpec bs) cn rv
      SymCtorReg bs cn sts       -> SymCtorReg (bindSpec bs) cn
                                      (map symbolicField sts)
      SymWeaken scp inScp st' bs -> SymWeaken (bindSpec scp) (bindSpec inScp)
                                      (symbolicTerm st') (bindSpec bs)
      SymSubst bs bv st1 st2     -> SymSubst (bindSpec bs) bv
                                      (symbolicTerm st1) (symbolicTerm st2)

    symbolicField :: SymbolicField w 'Checked -> SymbolicField w 'Grouped
    symbolicField sf = case sf of
      SymFieldSort loc scp st          -> SymFieldSort loc (bindSpec scp) (symbolicTerm st)
      SymFieldBinding loc bs bv        -> SymFieldBinding loc (bindSpec bs) bv
      SymFieldReferenceFree loc bs rv  -> SymFieldReferenceFree loc (bindSpec bs) rv
      SymFieldReferenceBound loc bs bv -> SymFieldReferenceBound loc (bindSpec bs) bv
      SymFieldEnv loc scp se           -> SymFieldEnv loc (bindSpec scp) (symbolicEnv se)
      SymFieldSet loc scp sz           -> SymFieldSet loc (bindSpec scp) (symbolicSet sz)

    symbolicEnv :: SymbolicEnv 'Checked -> SymbolicEnv 'Grouped
    symbolicEnv _se = case _se of
      SymEnvVar scp ev  -> SymEnvVar (bindSpec scp) ev
      SymEnvNil scp etn -> SymEnvNil (bindSpec scp) etn
      SymEnvCons scp se cn ntn sfs ->
        SymEnvCons (bindSpec scp) (symbolicEnv se) cn ntn (map symbolicField sfs)

    symbolicSet :: SymbolicSet 'Checked -> SymbolicSet 'Grouped
    symbolicSet _sz = case _sz of
      SymSetVar zv       -> SymSetVar zv
      SymSetCtor cn szfs -> SymSetCtor cn (map symbolicSet szfs)
