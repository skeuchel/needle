{-# LANGUAGE DataKinds #-}

module KnotCore.Elaboration.ObligationReg where

import Coq.StdLib
import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core

import Control.Applicative
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe

import Debug.Trace

obligations :: Elab m => [RelationDecl] -> [EnvDecl] -> m [Sentence]
obligations rds eds = concat <$> sequenceA
  [ eEnvDecl rd (typeNameOf ed) (typeNameOf bv) rtn
  | ed <- eds
  , EnvCtorCons _cn bv fds (Just (EnvCtorSubst rtn _varRule)) <- edCtors ed
  , rd <- rds
  , Prelude.not
    (null
      [ ()
      | r@RuleReg{} <- relRules rd
      , RuleMetavarFree fv _fvWf <- ruleMetavarBinders r
      , typeNameOf fv == typeNameOf bv
      ]
    )
  ]

eEnvDecl :: Elab m => RelationDecl -> EnvTypeName -> NamespaceTypeName -> RelationTypeName -> m [Sentence]
eEnvDecl rd etn ntn rtn = do
  let mbEv@(Just ev) = relEnv rd
  (stn,cn) <- getNamespaceCtor ntn

  methodDecls <-
    sequenceA
    [ do
        sub <- makeMetaVarSub ntn stn rmbs
        rmbs' <- traverse (elabRuleMetavarBinder sub) rmbs
        fmls' <- traverse (elabFormula etn ntn rtn sub) fmls
        jmt'   <- elabJudgement sub jmt
        binders0  <- sequenceA [toBinder ev]
        binders1  <- catMaybes <$> traverse eRuleMetavarBinder rmbs'
        binders2  <- traverse eFormula fmls'
        binders3' <- map snd . catMaybes <$> traverse (eRuleMetavarWellFormed (relEnv rd)) rmbs'
        binders3  <- traverse toBinder binders3'

        MethodDeclaration
          <$> idMethodObligationReg etn ntn cn
          <*> pure (binders0 ++ binders1 ++ binders2 ++ binders3)
          <*> eJudgement jmt'
    | RuleReg cn rmbs fmls jmt _outputs <- relRules rd
    , Prelude.not
      (null
        [ ()
        | RuleMetavarFree fv _fvWf <- rmbs
        , typeNameOf fv == ntn
        ]
      )
    ]

  classId <- idClassObligationReg etn ntn (relTypeName rd)
  classRef <- toRef classId
  classDecl <-
    ClassDeclaration
    <$> pure classId
    <*> pure []
    <*> pure (Just Prop)
    <*> pure methodDecls

  inst <- idInstObligationReg etn ntn (relTypeName rd)

  return
    [ SentenceClassDecl classDecl
    , SentenceContext [BinderImplicitNameType [NameIdent inst] classRef]
    ]

makeMetaVarSub :: Elab m => NamespaceTypeName -> SortTypeName -> [RuleMetavarBinder] -> m (Map FreeVariable SortVariable)
makeMetaVarSub ntn stn rmbs =
  M.fromList <$>
  sequenceA
    [ (,) fv <$> freshSortVariable stn
    | RuleMetavarFree fv _fvWf <- rmbs, typeNameOf fv == ntn
    ]

elabRuleMetavarBinder :: Elab m => Map FreeVariable SortVariable -> RuleMetavarBinder -> m RuleMetavarBinder
elabRuleMetavarBinder sub rmb = case rmb of
  RuleMetavarFree fv _fvWf
    | Just sv <- M.lookup fv sub ->
      RuleMetavarSort Nil sv <$> freshHypothesis <*> pure Nothing
    | otherwise -> pure rmb
  _ -> pure rmb

elabFormula :: Elab m => EnvTypeName -> NamespaceTypeName -> RelationTypeName -> Map FreeVariable SortVariable -> Formula -> m Formula
elabFormula etn ntn rtn sub fml = case fml of
  FormLookup lkv ev fv sfs
    | Just sv <- M.lookup fv sub -> do
        jmv <- freshJudgementVariable rtn
        pure $!
          FormJudgement jmv Nil
            (Judgement rtn (Just $ SymEnvVar ev) (SymFieldSort Nil Nil (SymSubtree Nil sv):sfs) [])
            []
  _ -> pure fml


elabJudgement :: Elab m => Map FreeVariable SortVariable -> Judgement -> m Judgement
elabJudgement sub (Judgement rtn mbEnv sfs outs) =
  Judgement rtn mbEnv <$> traverse (elabSymbolicField sub) sfs <*> pure outs

elabSymbolicField :: Elab m => Map FreeVariable SortVariable -> SymbolicField w -> m (SymbolicField w)
elabSymbolicField sub sf = case sf of
  SymFieldSort bs bs' st -> SymFieldSort bs bs' <$> elabSymbolicTerm sub st
  _ -> pure sf

elabSymbolicTerm :: Elab m => Map FreeVariable SortVariable -> SymbolicTerm -> m SymbolicTerm
elabSymbolicTerm sub st = case st of
  SymCtorVarFree bs cn fv
    | Just sv <- M.lookup fv sub ->
      pure $! SymWeaken bs Nil (SymSubtree Nil sv) bs
  SymCtorReg bs cn sfs ->
    SymCtorReg bs cn <$> traverse (elabSymbolicField sub) sfs
  _ -> pure st

eFormula :: Elab m => Formula -> m Binder
eFormula (FormJudgement jmv _ jmt _) = jvBinder jmv jmt
eFormula (FormLookup lkv _ _ _)      = toBinder lkv

eJudgement :: Elab m => Judgement -> m Term
eJudgement (Judgement rtn mbEnv sfs outs) = do
  fs <- catMaybes <$> traverse symbolicFieldToField sfs
  TermApp
    <$> toRef rtn
    <*> (concat <$> sequenceA
         [ traverse eSymbolicEnv (maybeToList mbEnv)
         , traverse toTerm fs
         , traverse (eSymbolicEnv . snd) outs
         ]
        )
