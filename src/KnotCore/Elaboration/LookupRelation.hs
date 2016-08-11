{-# LANGUAGE DataKinds #-}

module KnotCore.Elaboration.LookupRelation where

import Control.Applicative
import Data.Maybe

import qualified Coq.StdLib as Coq
import qualified Coq.Syntax as Coq

import KnotCore.Syntax
import KnotCore.LookupRelation
import KnotCore.Elaboration.Core
import qualified KnotCore.Elaboration.Lemma.LookupInversionHere as LookupInversionHere
import qualified KnotCore.Elaboration.Lemma.LookupFunctional as LookupFunctional
import qualified KnotCore.Elaboration.Lemma.LookupWellformedData as LookupWellformedData

mkLookupRelations :: Elab m => EnvDecl -> m [LookupRelation]
mkLookupRelations ed@(EnvDecl _ _ ecs) =
  catMaybes <$> traverse (mkLookupRelation ed) ecs

mkLookupRelation :: Elab m => EnvDecl -> EnvCtor -> m (Maybe LookupRelation)
mkLookupRelation (EnvDecl{})         (EnvCtorNil _) = return Nothing
mkLookupRelation (EnvDecl etn _ ecs) (EnvCtorCons hcn hmv hfds _mbHereRtn) = do

  hfds' <- freshen hfds
  here   <- localNames $
              LookupHere
                <$> pure hcn
                <*> freshen hmv
                <*> pure hfds'
  theres <- sequenceA
              [ localNames $
                  LookupThere
                    <$> pure hcn
                    <*> freshFreeVariable (typeNameOf hmv)
                    <*> freshen hfds
                    <*> pure tcn
                    <*> freshen tmv
                    <*> freshen tfields
              | EnvCtorCons tcn tmv tfields _mbThereRtn <- ecs
              ]
  return . Just $
    LookupRelation etn hcn
      (typeNameOf hmv)
      hfds'
      here theres

eLookupRelations :: Elab m => EnvDecl -> m [Coq.Sentence]
eLookupRelations ed = do
  lookups  <- mkLookupRelations ed
  rels     <- traverse eLookupRelation lookups
  invs     <- LookupInversionHere.lemmas lookups
  funcls   <- LookupFunctional.lemmas lookups
  wfs      <- LookupWellformedData.lemmas lookups
  return (rels ++ invs ++ funcls ++ wfs)

eLookupRelation :: Elab m => LookupRelation -> m Coq.Sentence
eLookupRelation (LookupRelation etn cn ntn fds here theres) =
  fmap (Coq.SentenceInductive . Coq.Inductive . (:[])) $
    Coq.InductiveBody
      <$> idTypeLookup cn
      <*> pure []
      <*> eLookupType etn ntn fds
      <*> sequenceA
            (eLookupHere etn here :
             map (eLookupThere etn) theres)

eLookupType :: Elab m =>
               EnvTypeName ->
               NamespaceTypeName ->
               [FieldDecl 'WOMV] ->
               m Coq.Term
eLookupType etn ntn fds =
  Coq.TermFunction
    <$> toRef etn
    <*> (Coq.TermFunction
           <$> typeIndex ntn
           <*> (Coq.prop <$> sequenceA (eFieldDeclTypes fds))
        )

eLookupHere :: Elab m => EnvTypeName -> LookupHere -> m Coq.InductiveCtor
eLookupHere etn (LookupHere cn mv hfds) = localNames $ do

  ev      <- freshEnvVariable etn
  (stn,_) <- getNamespaceCtor (typeNameOf mv)
  hfs <- eFieldDeclFields hfds
  let ntn = typeNameOf mv

  res <- toTerm (Lookup
                   (ECons (EVar ev) ntn hfs)
                   (I0 ntn stn)
                   (map (shiftField (C0 ntn)) hfs)
                )
  wfs <- sequenceA
         [ toTerm (WfSort (HVDomainEnv (EVar ev)) (SVar sv))
         | FieldDeclSort _ sv _ <- hfds
         ]

  Coq.InductiveCtor
    <$> (idCtorLookupHere cn >>= toId)
    <*> sequenceA
        ( toImplicitBinder ev :
          eFieldDeclBinders hfds
        )
    <*> pure (Just (foldr Coq.TermFunction res wfs))

eLookupThere :: Elab m => EnvTypeName -> LookupThere -> m Coq.InductiveCtor
eLookupThere etn (LookupThere hcn hmv hfds tcn tmv tfields) = localNames $ do

  ev      <- freshEnvVariable etn
  x       <- toIndex hmv
  hfs     <- eFieldDeclFields hfds
  tfs     <- eFieldDeclFields tfields

  let hntn = typeNameOf hmv
      tntn = typeNameOf tmv

  premise <- toTerm
             (Lookup (EVar ev) (IVar x) hfs)
  concl   <- toTerm
             (Lookup
                (ECons (EVar ev) tntn tfs)
                (if hntn == tntn
                   then IS (IVar x)
                   else IVar x)
                (map (shiftField (C0 (typeNameOf tmv))) hfs)
             )

  Coq.InductiveCtor
    <$> (idCtorLookupThere hcn tcn >>= toId)
    <*> sequenceA
        (toImplicitBinder ev:
          toImplicitBinder x:
          eFieldDeclBinders (hfds++tfields)
        )
    <*> pure (Just $ Coq.TermFunction premise concl)
