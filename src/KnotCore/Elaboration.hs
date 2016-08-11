{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

module KnotCore.Elaboration where

import qualified Coq.StdLib as Coq
import qualified Coq.Syntax as Coq

import           KnotCore.Syntax
import           KnotCore.Environment
import           KnotCore.Elaboration.Core
import           KnotCore.Elaboration.Hints

-- Sort related
import qualified KnotCore.Elaboration.Namespace as Namespace
import qualified KnotCore.Elaboration.HVarlist as HVarlist
import qualified KnotCore.Elaboration.Weaken as Weaken
import qualified KnotCore.Elaboration.Index as Index
import qualified KnotCore.Elaboration.TermSort as TermSort
import qualified KnotCore.Elaboration.Functions as Functions
import qualified KnotCore.Elaboration.Shift as Shift
import qualified KnotCore.Elaboration.Subst as Subst
import qualified KnotCore.Elaboration.Trace as Trace
import qualified KnotCore.Elaboration.Lemma.StabilityShift as StabilityShift
import qualified KnotCore.Elaboration.Lemma.StabilityWeaken as StabilityWeaken
import qualified KnotCore.Elaboration.Lemma.StabilitySubst as StabilitySubst
import qualified KnotCore.Elaboration.Interaction as Interaction

-- Well-formedness related
import qualified KnotCore.Elaboration.HVarlistInsertion as HVarlistInsertion
import qualified KnotCore.Elaboration.SubstHvlRelation as SubstHvlRelation
import qualified KnotCore.Elaboration.WellFormedIndex as WellFormedIndex
import qualified KnotCore.Elaboration.WellFormedTerm as WellFormedTerm
import qualified KnotCore.Elaboration.WellFormedTermInduction as WellFormedTermInduction
import qualified KnotCore.Elaboration.Lemma.ShiftWellFormedIndex as ShiftWellFormedIndex
import qualified KnotCore.Elaboration.Lemma.ShiftWellFormed as ShiftWellFormed
import qualified KnotCore.Elaboration.Lemma.WeakenWfTerm as WeakenWfTerm
import qualified KnotCore.Elaboration.Lemma.SubstHvlWfIndexHom as SubstHvlWfIndexHom
import qualified KnotCore.Elaboration.Lemma.SubstHvlWfIndexHet as SubstHvlWfIndexHet
import qualified KnotCore.Elaboration.Lemma.SubstHvlWfTerm as SubstHvlWfTerm
import qualified KnotCore.Elaboration.WellFormedInversion as HintsWellFormedInversion
import qualified KnotCore.Elaboration.Lemma.WellFormedStrengthen as WellFormedStrengthen
import qualified KnotCore.Elaboration.WellFormedTermCast as WellFormedTermCast
import qualified KnotCore.Elaboration.Lemma.WellFormedInversion as LemmaWellFormedInversion
import qualified KnotCore.Elaboration.SubHvl as SubHvl

-- Context related
import qualified KnotCore.Elaboration.TermEnv as TermEnv
import qualified KnotCore.Elaboration.ShiftEnv as ShiftEnv
import qualified KnotCore.Elaboration.SubstEnv as SubstEnv
import qualified KnotCore.Elaboration.WeakenEnv as WeakenEnv
import qualified KnotCore.Elaboration.LookupRelation as Lookup
import qualified KnotCore.Elaboration.InsertEnvRelation as InsertEnvRelation
import qualified KnotCore.Elaboration.SubstEnvRelation as SubstEnvRelation
import qualified KnotCore.Elaboration.Lemma.AppendEnvAssoc as AppendEnvAssoc
import qualified KnotCore.Elaboration.Lemma.DomainEnvAppendEnv as DomainEnvAppendEnv
import qualified KnotCore.Elaboration.Lemma.DomainEnvShiftEnv as DomainEnvShiftEnv
import qualified KnotCore.Elaboration.Lemma.DomainEnvSubstEnv as DomainEnvSubstEnv
import qualified KnotCore.Elaboration.Lemma.ShiftEnvAppendEnv as ShiftEnvAppendEnv
import qualified KnotCore.Elaboration.Lemma.SubstEnvAppendEnv as SubstEnvAppendEnv
import qualified KnotCore.Elaboration.Lemma.WeakenAppend as WeakenAppend
import qualified KnotCore.Elaboration.Lemma.InsertLookup as InsertLookup
import qualified KnotCore.Elaboration.Lemma.InsertEnvInsertHvl as InsertEnvInsertHvl
import qualified KnotCore.Elaboration.Lemma.SubstEnvSubstHvl as SubstEnvSubstHvl
import qualified KnotCore.Elaboration.Lemma.LookupInversionHere as LookupInversionHere
import qualified KnotCore.Elaboration.Lemma.LookupFunctional as LookupFunctional
import qualified KnotCore.Elaboration.Lemma.LookupWellformedIndex as LookupWellformedIndex
import qualified KnotCore.Elaboration.Lemma.WeakenLookup as WeakenLookup
import qualified KnotCore.Elaboration.Lemma.WeakenLookupHere as WeakenLookupHere
import qualified KnotCore.Elaboration.Lemma.SubstEnvLookupHet as SubstEnvLookupHet

import qualified KnotCore.Elaboration.Relation as Relation
import qualified KnotCore.Elaboration.Lemma.DomainOutput as DomainOutput
import qualified KnotCore.Elaboration.RelationCast as RelationCast
import qualified KnotCore.Elaboration.Shift.Relation as ShiftRelation
import qualified KnotCore.Elaboration.Lemma.WeakenRelation as WeakenRelation
import qualified KnotCore.Elaboration.Lemma.RelationWellFormed as RelationWellFormed
import qualified KnotCore.Elaboration.HintsRelationWellFormed as HintsRelationWellFormed
import qualified KnotCore.Elaboration.ObligationVar as ObligationVar
import qualified KnotCore.Elaboration.Lemma.SubstEnvLookup as SubstEnvLookup
import qualified KnotCore.Elaboration.ObligationReg as ObligationReg
import qualified KnotCore.Elaboration.Lemma.SubstEnvRelation as SubstEnvRelation

-- Size related
import qualified KnotCore.Elaboration.Size as Size
import qualified KnotCore.Elaboration.Lemma.ShiftSize as ShiftSize
import qualified KnotCore.Elaboration.Lemma.WeakenSize as WeakenSize

import           Control.Monad
import           Control.Monad.Error.Class
import           Control.Monad.Trans.Reader (ReaderT(..), ask)
import           Data.List (nub, intersect)

elaborateSpec :: (MonadError String m, EnvM m, FreshM m) => TermSpec -> m Coq.Root
elaborateSpec ts = runElabT (eTermSpec ts) (metaEnvironments ts)

newtype ElabT m a =
  ElabT { fromElabT :: ReaderT MetaEnvironments m a }
  deriving (Functor,Applicative)

instance MonadError String m => Monad (ElabT m) where
  return a      = ElabT (return a)
  ElabT m >>= f = ElabT (m >>= (fromElabT . f))
  fail s        = ElabT (throwError s)

deriving instance (MonadError String m, EnvM m) => EnvM (ElabT m)
deriving instance (MonadError String m, FreshM m) => FreshM (ElabT m)
deriving instance (MonadError String m) => MonadError String (ElabT m)


instance (EnvM m, FreshM m, MonadError String m) => Elab (ElabT m) where
  getMetaEnvironments   = ElabT ask
  liftMaybe _ (Just a)  = return a
  liftMaybe str Nothing = fail ("liftMaybe: " ++ str)

runElabT :: MonadError String m => ElabT m a -> MetaEnvironments -> m a
runElabT = runReaderT . fromElabT

--------------------------------------------------------------------------------

eTermSpec :: Elab m => TermSpec -> m Coq.Root
eTermSpec ts@(TermSpec nds _ sgds fgds eds rgds _zgds _subst) = do

  let section = Coq.SentenceSection
      blank   = Coq.SentenceBlankline

  -- Namespace elaboration
  namespace         <- Namespace.eNamespace nds
  hvarlist          <- HVarlist.eHVarlist
  index             <- Index.eIndex nds

  -- Term elaboration
  terms             <- TermSort.eSortGroupDecls sgds
  funs              <- Functions.eFunGroupDecls fgds

  shift             <- Shift.eShift ts
  weaken            <- Weaken.eWeaken ts
  trace             <- Trace.eTrace nds
  subst             <- Subst.eSubst ts
  size              <- Size.eSortGroupDecls sgds

  -- Term level lemmas
  stabilityShift              <- StabilityShift.lemmas fgds
  stabilityWeaken             <- StabilityWeaken.lemmas sgds
  stabilitySubst              <- StabilitySubst.lemmas fgds
  shiftSize                   <- ShiftSize.lemmas sgds
  weakenSize                  <- WeakenSize.lemmas

  -- Interaction lemmas
  interaction                 <- Interaction.lemmas nds sgds
  wfindex                     <- WellFormedIndex.eWellFormedIndex
  wfterm                      <- WellFormedTerm.eSortGroupDecls sgds
  wfinversion                 <- LemmaWellFormedInversion.lemmas sgds
  wfterminduction             <- WellFormedTermInduction.eSortGroupDecls sgds
  hvarlistinsertion           <- HVarlistInsertion.eHVarlistInsertions
  substHvlRelations           <- SubstHvlRelation.eSubstHvlRelations
  shiftwfindex                <- ShiftWellFormedIndex.lemmas
  shiftwfterm                 <- ShiftWellFormed.lemmas sgds
  weakenwfterm                <- WeakenWfTerm.lemmas sgds
  strengthenwfterm            <- WellFormedStrengthen.lemmas
  substwfindexhom             <- SubstHvlWfIndexHom.lemmas
  substwfindexhet             <- SubstHvlWfIndexHet.lemmas
  substwfterm                 <- SubstHvlWfTerm.lemmas sgds
  wellFormedTermCast          <- WellFormedTermCast.lemmas sgds

  ctx       <- concat <$> sequenceA
               [ traverse TermEnv.eEnvDecl eds
               , traverse TermEnv.eEnvAppend eds
               , traverse TermEnv.eEnvLength eds
               ]

  shiftEnvs          <- ShiftEnv.eShiftEnvs eds
  substEnvs          <- SubstEnv.eSubstEnvs eds
  weakenEnvs         <- traverse (WeakenEnv.eFunctionWeakenEnv.typeNameOf) eds
  appendEnvAssoc     <- AppendEnvAssoc.lemmas eds
  domainEnvAppendEnv <- DomainEnvAppendEnv.lemmas eds
  domainEnvShiftEnv  <- DomainEnvShiftEnv.lemmas eds
  domainEnvSubstEnv  <- DomainEnvSubstEnv.lemmas eds
  shiftEnvAppendEnv  <- ShiftEnvAppendEnv.lemmas eds
  substEnvAppendEnv  <- SubstEnvAppendEnv.lemmas eds
  weakenAppend       <- WeakenAppend.lemmas sgds

  lookups            <- concat <$> traverse Lookup.eLookupRelations eds
  weakenLookup       <- WeakenLookup.lemmass eds
  weakenLookupHere   <- WeakenLookupHere.lemmass eds

  insertenvrelations <- InsertEnvRelation.eInsertEnvRelationss eds
  substenvrelations  <- SubstEnvRelation.eSubstEnvRelationss eds

  insertLookups             <- InsertLookup.lemmass eds
  insertEnvInsertHvl        <- InsertEnvInsertHvl.lemmass eds
  substEnvSubstHvl          <- SubstEnvSubstHvl.lemmass eds
  substEnvLookupHet         <- SubstEnvLookupHet.lemmass eds
  -- lookupFunctional          <- LookupFunctional.lemmas lookups
  lookupWellformedIndex     <- concat <$> traverse LookupWellformedIndex.eLookupWellformedIndex eds
  -- lookupInversionHere       <- LookupInversionHere.lemmas lookups

  shiftFunIds   <- setFunctionShift
  fequalShiftHints <-
    sequenceA
    [ do
        fn <- Coq.TermApp
                <$> toRef shift
                <*> sequenceA [idFamilyCutoffZero >>= toRef]

        return $
          Coq.SentenceHint Coq.ModGlobal
            (Coq.HintResolve
             [ Coq.TermApp (Coq.termIdent "f_equal") [fn]
             ]
            )
            [Coq.ID "cong_shift0"]
    | shift <- shiftFunIds
    ]
  allFuns <- getFunctions
  let ntnsets = nub [ ntns | (_,_,ntns) <- allFuns ]
  subhvls <- concat <$> traverse SubHvl.eSubHvl ntnsets

  -- Hvl, Cutoff, Trace
  weakenCutoffAppendHints   <- setLemmaWeakenCutoffAppend           >>= mkRewriteHints      ["weakencutoff_append" ]
  weakenTraceAppendHints    <- setLemmaWeakenTraceAppend            >>= mkRewriteHints      ["weakentrace_append" ]

  -- Sort terms
  stabilityShiftHints       <- setLemmaStabilityShift               >>= mkRewriteHints      ["interaction", "stability_shift" ]
  stabilityWeakenHints      <- setLemmaStabilityWeaken              >>= mkRewriteHints      ["interaction", "stability_weaken" ]
  stabilitySubstHints       <- setLemmaStabilitySubst               >>= mkRewriteHints      ["interaction", "stability_subst" ]
  shiftSizeHints            <- setLemmaShiftSize                    >>= mkRewriteHints      ["interaction", "shift_size" ]
  weakenSizeHints           <- setLemmaWeakenSize                   >>= mkRewriteHints      ["interaction", "weaken_size" ]

  -- Well-formedness
  wellFormedTermHints       <- setRelationWellFormed                >>= mkConstructorsHints ["infra", "wf"]
  insertHvlHints            <- setTypeInsertHvl                     >>= mkConstructorsHints ["infra", "shift", "shift_wf", "wf"]
  weakenInsertHvlHints      <- setLemmaWeakenRelationHVarlistInsert >>= mkResolveHints      ["infra", "shift", "shift_wf", "weaken", "wf"]
  shiftwfindexHints         <- setLemmaShiftWellFormedIndex         >>= mkResolveHints      ["infra", "shift", "shift_wf", "wf"]
  shiftwftermHints          <- setLemmaShiftWellFormedSort          >>= mkResolveHints      ["infra", "shift", "shift_wf", "wf"]
  substHvlHints             <- setTypeSubstHvl                      >>= mkConstructorsHints ["infra", "subst", "subst_wf", "wf"]
  substwfindexHints         <- setLemmaSubstHvlWfIndex              >>= mkResolveHints      ["infra", "subst", "subst_wf", "wf"]
  substwftermHints          <- setLemmaSubstWellFormedSort          >>= mkResolveHints      ["infra", "subst", "subst_wf", "wf"]
  subhvlAppendHints         <- traverse idLemmaSubHvlAppend ntnsets >>= mkResolveHints      ["infra", "wf"]

  -- Environment terms
  domainEnvAppendEnvHints   <- setLemmaDomainEnvAppendEnv           >>= mkRewriteHints      ["interaction", "env_domain_append" ]
  domainEnvShiftEnvHints    <- setLemmaDomainEnvShiftEnv            >>= mkRewriteHints      ["interaction", "env_domain_shift" ]
  domainEnvSubstEnvHints    <- setLemmaDomainEnvSubstEnv            >>= mkRewriteHints      ["interaction", "env_domain_subst" ]
  shiftEnvAppendEnvHints    <- setLemmaShiftEnvAppendEnv            >>= mkRewriteHints      ["interaction", "env_shift_append" ]
  substEnvAppendEnvHints    <- setLemmaSubstEnvAppendEnv            >>= mkRewriteHints      ["interaction", "env_shift_append" ]

  -- TODO:Only lookup_here should be added to subst.
  insertEnvInsertHvlHints   <- setInsertEnvInsertHvl                >>= mkResolveHints      ["infra", "shift", "shift_wf", "wf"]
  insertEnvCtorHints        <- setTypeInsertEnv                     >>= mkConstructorsHints ["infra", "shift", "subst"]
  weakenInsertEnvHints      <- setLemmaWeakenInsertEnv              >>= mkResolveHints      ["infra", "shift"]
  lookupCtorHints           <- setTypeLookup                        >>= mkConstructorsHints ["infra", "lookup", "shift", "subst"]
  weakenLookupHints         <- setLemmaWeakenLookup                 >>= mkResolveHints      ["infra", "lookup", "shift", "weaken"]
  insertLookupHints         <- setLemmaInsertLookup                 >>= mkResolveHints      ["infra", "lookup", "shift"]
  lookupwfindexHints        <- setLemmaLookupWellformedIndex        >>= mkResolveHints      ["infra", "lookup", "wf"]
  lookupWellformedDataHints <- setLemmaLookupWellformedData         >>= mkResolveHints      ["infra", "wf"]
  substEnvCtorHints         <- setTypeSubstEnv                      >>= mkConstructorsHints ["infra", "subst"]
  weakenSubstEnvHints       <- setLemmaWeakenSubstEnv               >>= mkResolveHints      ["infra", "subst"]
  substEnvSubstHvlHints     <- setLemmaSubstEnvSubstHvl             >>= mkResolveHints      ["infra", "subst", "subst_wf", "wf", "substenv_substhvl"]
  substEnvLookupHints       <- setLemmaSubstEnvLookup               >>= mkResolveHints      ["infra", "lookup", "subst"]
  shiftRelationHints        <- setLemmaShiftRelation                >>= mkResolveHints      ["infra", "shift"]

  -- Hints to be used by the user
  appendEnvAssocHints <-
     setLemmaAppendEnvAssoc
     >>= mkRewriteHints ["interaction"]
  weakenAppendHints <- concat <$> sequence
    [ setLemmaWeakenCutoffAppend
    , setLemmaWeakenTraceAppend
    , setLemmaWeakenAppend
    , sequence [idLemmaHVarlistAppendAssoc]
    ] >>= mkRewriteRightToLeftHints ["interaction"]

  wellformedRelations <- setRelationWellFormed
  wellformedDomainAppendHints <-
    for wellformedRelations $ \wf -> localNames $ do
      qid <- toQualId wf

      return $ Coq.SentenceHint Coq.ModNone
        (Coq.HintExtern 10 (Just $ Coq.PatCtor qid [Coq.ID "_", Coq.ID "_"])
           (Coq.PrTactic "autorewrite with env_domain_append in *" []))
           [Coq.ID "infra", Coq.ID "wf"]
  hintsWellformedInversion <- HintsWellFormedInversion.eSortGroupDecls sgds

  allStns <- getSorts
  strengthenHintss <-
    for allStns $ \stn -> do
      deps <- getSortNamespaceDependencies stn
      sequenceA
        [ do
            qid <- idRelationWellFormed stn >>= toQualId
            lem <- idLemmaWellFormedStrengthen stn ntns >>= toRef
            h   <- freshVariable "H" Coq.true >>= toId

            hyp <- Coq.ContextHyp h
                   <$> (Coq.PatCtorEx qid
                        <$> sequenceA
                            [ Coq.PatCtor
                              <$> (idAppendHVarlist >>= toQualId)
                              <*> pure [ Coq.ID "_", Coq.ID "_" ]
                            , Coq.PatCtor
                              <$> (idFunctionWeakenTerm stn >>= toQualId)
                              <*> pure [ Coq.ID "_", Coq.ID "_" ]
                            ]
                       )
            return $ Coq.SentenceHint Coq.ModNone
              (Coq.HintExtern 2 (Just $ Coq.PatCtor qid [Coq.ID "_", Coq.ID "_"])
                (Coq.PrMatchGoal [Coq.ContextRule [hyp] Coq.PatUnderscore (Coq.PrApplyIn lem h)]))
              [Coq.ID "infra", Coq.ID "wf"]
        | ntns <- ntnsets
        , null (deps `intersect` ntns)
        ]
  let wellformedStrengthenHints = concat strengthenHintss

  relationGroups          <- traverse Relation.eRelationGroupDecl rgds
  domainOutput            <- DomainOutput.lemmas rgds
  relationCasts           <- RelationCast.lemmas rgds
  weakenRelations         <- WeakenRelation.lemmas rgds
  shiftRelationGroups     <- ShiftRelation.lemmas rgds
  relationWellFormed      <- RelationWellFormed.lemmas rgds
  hintsRelationWellFormed <- HintsRelationWellFormed.hints rgds
  obligationsVar          <- ObligationVar.obligations eds
  substEnvLookup          <- SubstEnvLookup.lemmass eds
  obligationReg           <- ObligationReg.obligations (concatMap rgRelations rgds) eds
  substEnvRelation        <- SubstEnvRelation.lemmass eds rgds

  return . Coq.Root . concat $
    [ [ blank
      , Coq.SentenceVerbatim "Local Set Asymmetric Patterns."
      , blank
      ]
    , [ section (Coq.ID "Namespace") namespace, blank
      , section (Coq.ID "HVarlist")  hvarlist,  blank
      , section (Coq.ID "Index")     index,     blank
      , section (Coq.ID "Terms")     terms,     blank
      , section (Coq.ID "Functions") funs,      blank
      , section (Coq.ID "Shift")     shift,     blank
      , section (Coq.ID "Weaken")    weaken,    blank
      ]
    , [ section (Coq.ID "Subst") $ trace ++ subst, blank ]
    , fequalShiftHints
    , weakenCutoffAppendHints
    , weakenTraceAppendHints
    -- Stability
    , stabilityShift
    , stabilityShiftHints
    , stabilityWeaken
    , stabilityWeakenHints
    , stabilitySubst
    , stabilitySubstHints
    , interaction
    , [ section (Coq.ID "WellFormed") $ concat
        [ [wfindex]
        , wfterm
        , wfinversion
        , wfterminduction
        ]
      , section (Coq.ID "ShiftWellFormed") $ concat
        [ hvarlistinsertion
        , shiftwfindex
        , shiftwfterm
        , weakenwfterm
        ]
      ]
    , wellFormedTermCast
    , shiftwfindexHints
    , shiftwftermHints
    , insertHvlHints
    , weakenInsertHvlHints
    , [ section (Coq.ID "SubstWellFormed") $ concat
        [ substHvlRelations
        , substwfindexhom
        , substwfindexhet
        , substwfterm
        ]
      ]
    , substwfindexHints
    , substwftermHints
    , substHvlHints
    , subhvls
    , subhvlAppendHints
    , strengthenwfterm
    , wellformedStrengthenHints
    , [ section (Coq.ID "Context") $ concat
        [ ctx
        , appendEnvAssoc
        , domainEnvAppendEnv
        , shiftEnvs
        , weakenEnvs
        , substEnvs
        , domainEnvShiftEnv
        , domainEnvSubstEnv
        ]
      ]
    , domainEnvAppendEnvHints
    , [ section (Coq.ID "ContextStuff") $ concat
        [ [section (Coq.ID "ShiftEnvAppendEnv") shiftEnvAppendEnv]
        , [section (Coq.ID "SubstEnvAppendEnv") substEnvAppendEnv]
        , weakenAppend
        , [section (Coq.ID "Lookups") $ concat
           [ lookups
           , weakenLookup
           , lookupWellformedIndex
           ]
          ]
        , insertenvrelations
        , insertEnvInsertHvl
        , substenvrelations
        , substEnvSubstHvl
        ]
      ]
    , domainEnvShiftEnvHints
    , domainEnvSubstEnvHints
    , shiftEnvAppendEnvHints
    , substEnvAppendEnvHints
    , lookupCtorHints
    , weakenLookupHints
    , weakenLookupHere
    , wellFormedTermHints
    , wellformedDomainAppendHints
    , hintsWellformedInversion
    , lookupWellformedDataHints
    , lookupwfindexHints
    , insertEnvCtorHints
    , weakenInsertEnvHints
    , insertEnvInsertHvlHints
    , substEnvCtorHints
    , weakenSubstEnvHints
    , substEnvSubstHvlHints
    , insertLookups
    , insertLookupHints
    , substEnvLookupHet
    , substEnvLookupHints
    , size
    , shiftSize
    , shiftSizeHints
    , weakenSize
    , weakenSizeHints
    , relationGroups
    , domainOutput
    , relationCasts
    , shiftRelationGroups
    , shiftRelationHints
    , weakenRelations
    , relationWellFormed
    , hintsRelationWellFormed
    , obligationsVar
    , substEnvLookup
    , obligationReg
    , substEnvRelation
    , appendEnvAssocHints
    , weakenAppendHints
    ]
