
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
  catMaybes <$> mapM (mkLookupRelation ed) ecs

mkLookupRelation :: Elab m => EnvDecl -> EnvCtor -> m (Maybe LookupRelation)
mkLookupRelation (EnvDecl _ _ _)     (EnvCtorNil _) = return Nothing
mkLookupRelation (EnvDecl etn _ ecs) (EnvCtorCons hcn hmv hfields) = do

  here   <- localNames $
              LookupHere
                <$> pure hcn
                <*> freshen hmv
                <*> freshen hfields
  theres <- sequence
              [ localNames $
                  LookupThere
                    <$> pure hcn
                    <*> freshen hmv
                    <*> freshen hfields
                    <*> pure tcn
                    <*> freshen tmv
                    <*> freshen tfields
              | EnvCtorCons tcn tmv tfields <- ecs
              ]
  return . Just $
    LookupRelation etn hcn
      (typeNameOf hmv)
      (map typeNameOf hfields)
      here theres

eLookupRelations :: Elab m => EnvDecl -> m [Coq.Sentence]
eLookupRelations ed = do
  lookups  <- mkLookupRelations ed
  rels     <- mapM eLookupRelation lookups
  invs     <- LookupInversionHere.lemmas lookups
  funcls   <- LookupFunctional.lemmas lookups
  wfs      <- LookupWellformedData.lemmas lookups
  return (rels ++ invs ++ funcls ++ wfs)

eLookupRelation :: Elab m => LookupRelation -> m Coq.Sentence
eLookupRelation (LookupRelation etn cn ntn stns here theres) =
  fmap (Coq.SentenceInductive . Coq.Inductive . (:[])) $
    Coq.InductiveBody
      <$> idTypeLookup cn
      <*> pure []
      <*> eLookupType etn ntn stns
      <*> sequence
            (eLookupHere etn here :
             map (eLookupThere etn) theres)

eLookupType :: Elab m =>
               EnvTypeName ->
               NamespaceTypeName ->
               [SortTypeName] ->
               m Coq.Term
eLookupType etn ntn stns =
  Coq.TermFunction
    <$> toRef etn
    <*> (Coq.TermFunction
           <$> typeIndex ntn
           <*> (Coq.prop <$> mapM toRef stns))

eLookupHere :: Elab m => EnvTypeName -> LookupHere -> m Coq.InductiveCtor
eLookupHere etn (LookupHere cn mv fields) = localNames $ do

  ev      <- freshEnvVar etn
  (stn,_) <- getNamespaceCtor (typeNameOf mv)

  let ntn = typeNameOf mv
      ts  = map SVar fields

  res <- toTerm (Lookup
                   (ECtor cn (EVar ev) ts)
                   (I0 ntn stn)
                   (map (SShift' (C0 ntn)) ts)
                )
  wfs <- mapM (toTerm . WfTerm (HVDomainEnv (EVar ev))) ts

  Coq.InductiveCtor
    <$> (idCtorLookupHere cn >>= toId)
    <*> sequence (toImplicitBinder ev:map toImplicitBinder fields)
    <*> pure (Just (foldr Coq.TermFunction res wfs))

eLookupThere :: Elab m => EnvTypeName -> LookupThere -> m Coq.InductiveCtor
eLookupThere etn (LookupThere hcn hmv hfields tcn tmv tfields) = localNames $ do

  ev      <- freshEnvVar etn
  x       <- toIndex hmv

  let hntn = typeNameOf hmv
      tntn = typeNameOf tmv
      hts  = map SVar hfields
      tts  = map SVar tfields

  premise <- toTerm (Lookup (EVar ev) (IVar x) hts)
  concl   <- toTerm (Lookup
                      (ECtor tcn (EVar ev) tts)
                      (if hntn == tntn
                       then IS (IVar x)
                       else IVar x)
                      (map (SShift' (C0 (typeNameOf tmv))) hts))

  Coq.InductiveCtor
    <$> (idCtorLookupThere hcn tcn >>= toId)
    <*> sequence (toImplicitBinder ev:
                  toImplicitBinder x:
                  map toImplicitBinder (hfields++tfields))
    <*> pure (Just $ Coq.TermFunction premise concl)
