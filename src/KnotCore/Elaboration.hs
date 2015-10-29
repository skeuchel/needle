
module KnotCore.Elaboration where

import Control.Applicative
import Control.Monad
import Data.List (nub, intersect)
import qualified Coq.StdLib as Coq
import qualified Coq.Syntax as Coq

import KnotCore.Syntax
import KnotCore.Environment
import KnotCore.Elaboration.Core

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
import qualified KnotCore.Elaboration.Lemma.ShiftIndexCommInd as ShiftIndexCommInd
import qualified KnotCore.Elaboration.Lemma.ShiftCommInd as ShiftCommInd
import qualified KnotCore.Elaboration.Lemma.ShiftCommInd2 as ShiftCommInd2
import qualified KnotCore.Elaboration.Lemma.ShiftComm as ShiftComm
import qualified KnotCore.Elaboration.Lemma.WeakenShift as WeakenShift
import qualified KnotCore.Elaboration.Lemma.WeakenSubst as WeakenSubst
import qualified KnotCore.Elaboration.Lemma.WeakenAppend as WeakenAppend
import qualified KnotCore.Elaboration.Lemma.SubstIndexShiftIndexReflectionInd as SubstIndexShiftIndexReflectionInd
import qualified KnotCore.Elaboration.Lemma.SubstShiftReflectionInd as SubstShiftReflectionInd
import qualified KnotCore.Elaboration.Lemma.SubstShiftReflectionInd2 as SubstShiftReflectionInd2
import qualified KnotCore.Elaboration.Lemma.SubstShiftReflection as SubstShiftReflection
import qualified KnotCore.Elaboration.Lemma.ShiftSubstIndexCommInd as ShiftSubstIndexCommInd
import qualified KnotCore.Elaboration.Lemma.ShiftSubstCommInd as ShiftSubstCommInd
import qualified KnotCore.Elaboration.Lemma.ShiftSubstCommInd2 as ShiftSubstCommInd2
import qualified KnotCore.Elaboration.Lemma.ShiftSubstComm as ShiftSubstComm
import qualified KnotCore.Elaboration.Lemma.SubstShiftIndexCommInd as SubstShiftIndexCommInd
import qualified KnotCore.Elaboration.Lemma.SubstShiftCommInd as SubstShiftCommInd
import qualified KnotCore.Elaboration.Lemma.SubstShiftCommInd2 as SubstShiftCommInd2
import qualified KnotCore.Elaboration.Lemma.SubstSubordInd as SubstSubordInd
import qualified KnotCore.Elaboration.Lemma.SubstSubordInd2 as SubstSubordInd2
import qualified KnotCore.Elaboration.Lemma.SubstShiftComm as SubstShiftComm
import qualified KnotCore.Elaboration.Lemma.SubstSubord as SubstSubord
import qualified KnotCore.Elaboration.Lemma.SubstSubstIndexCommInd as SubstSubstIndexCommInd
import qualified KnotCore.Elaboration.Lemma.SubstSubstIndexCommLeftInd as SubstSubstIndexCommLeftInd
import qualified KnotCore.Elaboration.Lemma.SubstSubstCommInd as SubstSubstCommInd
import qualified KnotCore.Elaboration.Lemma.SubstSubstCommInd2 as SubstSubstCommInd2
import qualified KnotCore.Elaboration.Lemma.SubstSubstComm as SubstSubstComm

-- Well-formedness related
import qualified KnotCore.Elaboration.HVarlistInsertion as HVarlistInsertion
import qualified KnotCore.Elaboration.SubstHvlRelation as SubstHvlRelation
import qualified KnotCore.Elaboration.WellFormedIndex as WellFormedIndex
import qualified KnotCore.Elaboration.WellFormedTerm as WellFormedTerm
import qualified KnotCore.Elaboration.WellFormedTermInduction as WellFormedTermInduction
import qualified KnotCore.Elaboration.Lemma.ShiftWellFormedIndex as ShiftWellFormedIndex
import qualified KnotCore.Elaboration.Lemma.ShiftWellFormed as ShiftWellFormed
import qualified KnotCore.Elaboration.Lemma.SubstHvlWfIndexHom as SubstHvlWfIndexHom
import qualified KnotCore.Elaboration.Lemma.SubstHvlWfIndexHet as SubstHvlWfIndexHet
import qualified KnotCore.Elaboration.Lemma.SubstHvlWfTerm as SubstHvlWfTerm
import qualified KnotCore.Elaboration.WellFormedInversion as WellFormedInversion
import qualified KnotCore.Elaboration.Lemma.WellFormedStrengthen as WellFormedStrengthen

-- Context related
import qualified KnotCore.Elaboration.TermEnv as TermEnv
import qualified KnotCore.Elaboration.ShiftEnv as ShiftEnv
import qualified KnotCore.Elaboration.SubstEnv as SubstEnv
import qualified KnotCore.Elaboration.LookupRelation as Lookup
import qualified KnotCore.Elaboration.InsertEnvRelation as InsertEnvRelation
import qualified KnotCore.Elaboration.SubstEnvRelation as SubstEnvRelation
import qualified KnotCore.Elaboration.Lemma.AppendEnvAssoc as AppendEnvAssoc
import qualified KnotCore.Elaboration.Lemma.DomainEnvAppendEnv as DomainEnvAppendEnv
import qualified KnotCore.Elaboration.Lemma.DomainEnvShiftEnv as DomainEnvShiftEnv
import qualified KnotCore.Elaboration.Lemma.DomainEnvSubstEnv as DomainEnvSubstEnv
import qualified KnotCore.Elaboration.Lemma.ShiftEnvAppendEnv as ShiftEnvAppendEnv
import qualified KnotCore.Elaboration.Lemma.SubstEnvAppendEnv as SubstEnvAppendEnv
import qualified KnotCore.Elaboration.Lemma.InsertLookup as InsertLookup
import qualified KnotCore.Elaboration.Lemma.InsertEnvInsertHvl as InsertEnvInsertHvl
import qualified KnotCore.Elaboration.Lemma.SubstEnvSubstHvl as SubstEnvSubstHvl
import qualified KnotCore.Elaboration.Lemma.LookupInversionHere as LookupInversionHere
import qualified KnotCore.Elaboration.Lemma.LookupFunctional as LookupFunctional
import qualified KnotCore.Elaboration.Lemma.LookupWellformedIndex as LookupWellformedIndex
import qualified KnotCore.Elaboration.Lemma.WeakenLookup as WeakenLookup
import qualified KnotCore.Elaboration.Lemma.WeakenLookupHere as WeakenLookupHere
import qualified KnotCore.Elaboration.Lemma.SubstEnvLookupHet as SubstEnvLookupHet

-- Size related
import qualified KnotCore.Elaboration.Size as Size
import qualified KnotCore.Elaboration.Lemma.ShiftSize as ShiftSize
import qualified KnotCore.Elaboration.Lemma.WeakenSize as WeakenSize

import qualified KnotCore.Elaboration.SubHvl as SubHvl
--import qualified KnotCore.Elaboration.Relation as Relation

elaborateSpec :: TermSpec -> Coq.Root
elaborateSpec ts =
  case runElM (eTermSpec ts) (metaEnvironments ts) of
    Left err -> error $ "Elaboration failed: " ++ err
    Right r  -> r

eTermSpec :: TermSpec -> ElM Coq.Root
eTermSpec ts@(TermSpec nds _ sgds fgds eds _) = do

  let section = Coq.SentenceSection
      blank   = Coq.SentenceBlankline
      fds     = [ fd
                | fgd <- fgds
                , (_, fds) <- fgdFuns fgd
                , fd <- fds
                ]

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
  shiftIndexCommInd           <- ShiftIndexCommInd.lemmas nds
  shiftCommInd                <- ShiftCommInd.lemmas sgds
  shiftCommInd2               <- ShiftCommInd2.lemmas sgds
  shiftComm                   <- ShiftComm.lemmas sgds
  substIndexShiftIndexInd     <- SubstIndexShiftIndexReflectionInd.lemmas nds
  substShiftReflectionInd     <- SubstShiftReflectionInd.lemmas sgds
  substShiftReflectionInd2    <- SubstShiftReflectionInd2.lemmas sgds
  substShiftReflection        <- SubstShiftReflection.lemmas sgds
  shiftSubstIndexCommInd      <- ShiftSubstIndexCommInd.lemmas nds
  shiftSubstCommInd           <- ShiftSubstCommInd.lemmas sgds
  shiftSubstCommInd2          <- ShiftSubstCommInd2.lemmas sgds
  shiftSubstComm              <- ShiftSubstComm.lemmas sgds
  substShiftIndexCommInd      <- SubstShiftIndexCommInd.lemmas nds
  substShiftCommInd           <- SubstShiftCommInd.lemmas sgds
  substShiftCommInd2          <- SubstShiftCommInd2.lemmas sgds
  substSubordInd              <- SubstSubordInd.lemmas sgds
  substSubordInd2             <- SubstSubordInd2.lemmas sgds
  substShiftComm              <- SubstShiftComm.lemmas sgds
  substSubord                 <- SubstSubord.lemmas sgds
  substSubstIndexCommRightInd <- SubstSubstIndexCommInd.lemmas nds
  substSubstIndexCommLeftInd  <- SubstSubstIndexCommLeftInd.lemmas nds
  substSubstCommInd           <- SubstSubstCommInd.lemmas sgds
  substSubstCommInd2          <- SubstSubstCommInd2.lemmas sgds
  substSubstComm              <- SubstSubstComm.lemmas sgds
  weakenShift                 <- WeakenShift.lemmas sgds
  weakenSubst                 <- WeakenSubst.lemmas sgds
  weakenAppend                <- WeakenAppend.lemmas sgds
  shiftSize                   <- ShiftSize.lemmas sgds
  weakenSize                  <- WeakenSize.lemmas
  wfindex                     <- WellFormedIndex.eWellFormedIndex
  wfterm                      <- WellFormedTerm.eSortGroupDecls sgds
  wfterminduction             <- WellFormedTermInduction.eSortGroupDecls sgds
  hvarlistinsertion           <- HVarlistInsertion.eHVarlistInsertions
  substHvlRelations           <- SubstHvlRelation.eSubstHvlRelations
  shiftwfindex                <- ShiftWellFormedIndex.lemmas
  shiftwfterm                 <- ShiftWellFormed.lemmas sgds
  strengthenwfterm            <- WellFormedStrengthen.lemmas
  substwfindexhom             <- SubstHvlWfIndexHom.lemmas
  substwfindexhet             <- SubstHvlWfIndexHet.lemmas
  substwfterm                 <- SubstHvlWfTerm.lemmas sgds

  ctx       <- concat <$> sequence
               [ mapM TermEnv.eEnvDecl eds
               , mapM TermEnv.eEnvAppend eds
               , mapM TermEnv.eEnvLength eds
               ]

  appendEnvAssoc     <- AppendEnvAssoc.lemmas eds
  domainEnvAppendEnv <- DomainEnvAppendEnv.lemmas eds
  domainEnvShiftEnv  <- DomainEnvShiftEnv.lemmas eds
  domainEnvSubstEnv  <- DomainEnvSubstEnv.lemmas eds
  shiftEnvAppendEnv  <- ShiftEnvAppendEnv.lemmas eds
  substEnvAppendEnv  <- SubstEnvAppendEnv.lemmas eds
  shiftEnvs          <- ShiftEnv.eShiftEnvs eds
  substEnvs          <- SubstEnv.eSubstEnvs eds

  lookups            <- concat <$> mapM Lookup.eLookupRelations eds
  weakenLookup       <- WeakenLookup.lemmass eds
  weakenLookupHere   <- WeakenLookupHere.lemmass eds

  insertenvrelations <- InsertEnvRelation.eInsertEnvRelationss eds
  substenvrelations  <- SubstEnvRelation.eSubstEnvRelationss eds

  insertLookups             <- InsertLookup.lemmass eds
  insertEnvInsertHvl        <- InsertEnvInsertHvl.lemmass eds
  substEnvSubstHvl          <- SubstEnvSubstHvl.lemmass eds
  substEnvLookupHet         <- SubstEnvLookupHet.lemmass eds
  -- lookupFunctional          <- LookupFunctional.lemmas lookups
  lookupWellformedIndex     <- concat <$> mapM LookupWellformedIndex.eLookupWellformedIndex eds
  -- lookupInversionHere       <- LookupInversionHere.lemmas lookups
  {-
  relations          <- mapM Relation.eRelationDecl rds
  -}

  shiftFunIds   <- setFunctionShift
  fequalShiftHints <-
    sequence
    [ do
        fn <- Coq.TermApp
                <$> toRef shift
                <*> sequence [idFamilyCutoffZero >>= toRef]

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
  subhvls <- concat <$> mapM SubHvl.eSubHvl ntnsets

  let mkRewriteHints :: [String] -> [Coq.Identifier] -> ElM [Coq.Sentence]
      mkRewriteHints _   []  = return []
      mkRewriteHints dbs ids = do
        tms <- mapM toRef ids
        return
          [ Coq.SentenceHint Coq.ModNone (Coq.HintRewrite tms) [Coq.ID db]
          | db <- dbs
          ]
      mkResolveHints :: [String] -> [Coq.Identifier] -> ElM [Coq.Sentence]
      mkResolveHints _   []  = return []
      mkResolveHints dbs ids = do
        tms <- mapM toRef ids
        return
          [ Coq.SentenceHint Coq.ModNone (Coq.HintResolve tms) [Coq.ID db]
          | db <- dbs
          ]
      mkConstructorsHints :: [String] -> [Coq.Identifier] -> ElM [Coq.Sentence]
      mkConstructorsHints _   []  = return []
      mkConstructorsHints dbs ids =
        return
          [ Coq.SentenceHint Coq.ModNone (Coq.HintConstructors ids) [Coq.ID db]
          | db <- dbs
          ]

  -- Hvl, Cutoff, Trace
  weakenCutoffAppendHints   <- setLemmaWeakenCutoffAppend           >>= mkRewriteHints      ["interaction", "weakencutoff_append" ]
  weakenTraceAppendHints    <- setLemmaWeakenTraceAppend            >>= mkRewriteHints      ["interaction", "weakentrace_append" ]

  -- Sort terms
  stabilityShiftHints       <- setLemmaStabilityShift               >>= mkRewriteHints      ["interaction", "stability_shift" ]
  stabilityWeakenHints      <- setLemmaStabilityWeaken              >>= mkRewriteHints      ["interaction", "stability_weaken" ]
  stabilitySubstHints       <- setLemmaStabilitySubst               >>= mkRewriteHints      ["interaction", "stability_subst" ]
  substShiftReflectionHints <- setLemmaSubstShiftReflection         >>= mkRewriteHints      ["interaction", "reflection"]
  shiftCommHints            <- setLemmaShiftComm                    >>= mkRewriteHints      ["interaction", "shift_shift0" ]
  substShiftCommHints       <- setLemmaSubstShiftComm               >>= mkRewriteHints      ["interaction", "subst_shift0" ]
  substSubordHints          <- setLemmaSubstSubord                  >>= mkRewriteHints      ["interaction", "subst_shift0" ]
  shiftSubstCommHints       <- setLemmaShiftSubstComm               >>= mkRewriteHints      ["interaction", "shift_subst0" ]
  substSubstCommHints       <- setLemmaSubstSubstComm               >>= mkRewriteHints      ["interaction", "subst_subst0" ]
  weakenShiftHints          <- setLemmaWeakenShift                  >>= mkRewriteHints      ["weaken_shift" ]
  weakenSubstHints          <- setLemmaWeakenSubst                  >>= mkRewriteHints      ["weaken_subst" ]
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
  subhvlAppendHints         <- (mapM idLemmaSubHvlAppend ntnsets)   >>= mkResolveHints      ["infra", "wf"]

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

  wellformedRelations <- setRelationWellFormed
  wellformedDomainAppendHints <-
    forM wellformedRelations $ \wf -> localNames $ do
      qid <- toQualId wf

      return $ Coq.SentenceHint Coq.ModNone
        (Coq.HintExtern 10 (Just $ Coq.PatCtor qid [Coq.ID "_", Coq.ID "_"])
           (Coq.PrTactic "autorewrite with env_domain_append in *" []))
           [Coq.ID "infra", Coq.ID "wf"]
  wellformedInversionHints <- WellFormedInversion.eSortGroupDecls sgds

  allStns <- getSorts
  strengthenHintss <-
    forM allStns $ \stn -> do
      deps <- getSortNamespaceDependencies stn
      sequence
        [ do
            qid <- idRelationWellFormed stn >>= toQualId
            lem <- idLemmaWellFormedStrengthen stn ntns >>= toRef
            h   <- freshVariable "H" Coq.true >>= toId

            hyp <- Coq.ContextHyp h
                   <$> (Coq.PatCtorEx qid
                        <$> sequence
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
        , null (intersect deps ntns)
        ]
  let wellformedStrengthenHints = concat strengthenHintss

  return . Coq.Root . concat $
    [ [ section (Coq.ID "Namespace") namespace,    blank
      , section (Coq.ID "HVarlist")  hvarlist,     blank
      , section (Coq.ID "Index")     index,        blank
      , section (Coq.ID "Terms")     terms,        blank
      , section (Coq.ID "Functions") funs,         blank
      , section (Coq.ID "Shift")     shift,        blank
      , section (Coq.ID "Weaken")    weaken,       blank
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
    -- Interaction
    , [ section (Coq.ID "SubstShiftReflection") $ concat
        [ substIndexShiftIndexInd
        , substShiftReflectionInd2
        , substShiftReflection
        ]
      , section (Coq.ID "ShiftInteraction")
        [ section (Coq.ID "ShiftIndexCommInd") shiftIndexCommInd
        , section (Coq.ID "ShiftCommInd") shiftCommInd2
        , section (Coq.ID "ShiftComm") shiftComm
        ]
      ]
    , shiftCommHints
    , [ section (Coq.ID "WeakenShift") weakenShift
      , section (Coq.ID "ShiftSubstInteraction")
        [ section (Coq.ID "ShiftSubstIndexCommInd") shiftSubstIndexCommInd
        , section (Coq.ID "ShiftSubstCommInd") shiftSubstCommInd2
        , section (Coq.ID "ShiftSubstComm") shiftSubstComm
        , section (Coq.ID "SubstShiftIndexCommInd") substShiftIndexCommInd
        , section (Coq.ID "SubstShiftCommInd") substShiftCommInd2
        , section (Coq.ID "SubstShiftComm") substShiftComm
        , section (Coq.ID "SubstSubordInd") substSubordInd2
        , section (Coq.ID "SubstSubord") substSubord
        ]
      ]
    , substShiftReflectionHints
    , substShiftCommHints
    , substSubordHints
    , shiftSubstCommHints
    , [ section (Coq.ID "SubstSubstInteraction")
        [ section (Coq.ID "SubstSubstIndexCommInd") $
            substSubstIndexCommRightInd ++ substSubstIndexCommLeftInd
        , section (Coq.ID "SubstSubstCommInd") substSubstCommInd2
        , section (Coq.ID "SubstSubstComm") substSubstComm
        , section (Coq.ID "WeakenSubst") weakenSubst
        , section (Coq.ID "WeakenAppend") weakenAppend
        ]
      ]
    , substSubstCommHints
    , weakenShiftHints
    , weakenSubstHints
    , [ section (Coq.ID "WellFormed") $ concat
        [ [wfindex]
        , wfterm
        , wfterminduction
        ]
      , section (Coq.ID "ShiftWellFormed") $ concat
        [ hvarlistinsertion
        , shiftwfindex
        , shiftwfterm
        ]
      ]
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
        , substEnvs
        , domainEnvShiftEnv
        , domainEnvSubstEnv
        ]
      ]
    , domainEnvAppendEnvHints
    , [ section (Coq.ID "ContextStuff") $ concat
        [ [section (Coq.ID "ShiftEnvAppendEnv") shiftEnvAppendEnv]
        , [section (Coq.ID "SubstEnvAppendEnv") substEnvAppendEnv]
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
    , wellformedInversionHints
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
      -- relations,
    ]
