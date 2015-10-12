
module KnotCore.Elaboration.Lemma.SubstSubord where

import Control.Applicative
import Data.List ((\\))
import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core

lemmas :: Elab m => [SortGroupDecl] -> m [Sentence]
lemmas sdgs = do
  ntns <- getNamespaces
  concat <$> sequence
    [ do
        (stna,_) <- getNamespaceCtor ntna
        depsa <- getSortNamespaceDependencies stna
        sequence
          [ sortDecl ntna ntnb sd
          | ntnb <- ntns \\ depsa
          ]
    | SortGroupDecl _ sds deps _ <- sdgs,
      sd <- sds,
      ntna <- deps
    ]

sortDecl :: Elab m => NamespaceTypeName -> NamespaceTypeName -> SortDecl -> m Sentence
sortDecl ntna ntnb (SortDecl stn _ _) = localNames $ do

  (stna,_) <- getNamespaceCtor ntna

  xa      <- freshTraceVar ntna
  ta      <- freshSubtreeVar stna
  t       <- freshSubtreeVar stn

  let left   = SSubst (TS ntnb (TVar xa)) (SVar ta) (SVar t)
      right  = SSubst (TVar xa) (SVar ta) (SVar t)

  assertion <-
    TermForall
      <$> sequence [toBinder xa, toBinder ta]
      <*> (TermEq <$> toTerm left <*> toTerm right)

  definition <-
    Definition
    <$> idLemmaSubstSubord ntna ntnb stn
    <*> sequence [toBinder t]
    <*> pure (Just assertion)
    <*> (TermApp
         <$> (idLemmaSubstSubordInd ntna ntnb stn >>= toRef)
         <*> sequence [toRef t, toTerm HV0]
        )

  return $ SentenceDefinition definition
