{-# LANGUAGE GADTs #-}

module KnotCore.Elaboration.Lemma.WellFormedStrengthen where

import Control.Applicative
import Control.Monad
import Data.List (intersect, nub)
import Data.Maybe (catMaybes)
import Coq.Syntax
import Coq.StdLib

import KnotCore.Syntax
import KnotCore.Elaboration.Core

lemmas :: Elab m => m [Sentence]
lemmas = do
  stns <- getSorts
  allFuns <- getFunctions
  let ntnsets = nub [ ntns | (_,_,ntns) <- allFuns ]
  lemss <- for stns $ \stn -> do
             deps <- getSortNamespaceDependencies stn
             sequenceA
               [ eWellFormedStrengthen stn ntns
               | ntns <- ntnsets
               , null (deps `intersect` ntns)
               ]

  return $ concat lemss

eWellFormedStrengthen :: Elab m => SortTypeName -> [NamespaceTypeName] -> m Sentence
eWellFormedStrengthen stn ntns = do

  strengthen   <- idLemmaWellFormedStrengthen stn ntns
  k1           <- freshHVarlistVar
  k2           <- freshHVarlistVar
  t            <- freshSortVariable stn

  assertion <-
    TermForall
    <$> sequenceA [toBinder k2, toBinder k1, toBinder t]
    <*> (foldr1 TermFunction <$>
         sequenceA
         [ toTerm (SubHvl ntns (HVVar k2))
         , toTerm (WfSort
                     (HVAppend (HVVar k1) (HVVar k2))
                     (SWeaken (SVar t) (HVVar k2)))
         , toTerm (WfSort (HVVar k1) (SVar t))
         ]
        )

  proof <- sequenceA
    [ pure $ PrTactic "needleGenericWellformedStrengthen" []
    ]

  return $
    SentenceAssertionProof
      (Assertion AssLemma strengthen [] assertion)
      (ProofQed proof)
