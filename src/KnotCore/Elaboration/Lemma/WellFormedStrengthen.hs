
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
  lemss <- forM stns $ \stn -> do
             deps <- getSortNamespaceDependencies stn
             sequence
               [ eWellFormedStrengthen stn ntns
               | ntns <- ntnsets
               , null (intersect deps ntns)
               ]

  return $ concat lemss

eWellFormedStrengthen :: Elab m => SortTypeName -> [NamespaceTypeName] -> m Sentence
eWellFormedStrengthen stn ntns = do

  strengthen   <- idLemmaWellFormedStrengthen stn ntns
  k1           <- freshHVarlistVar
  k2           <- freshHVarlistVar
  t            <- freshSubtreeVar stn

  assertion <-
    TermForall
    <$> sequence [toBinder k2, toBinder k1, toBinder t]
    <*> (foldr1 TermFunction <$>
         sequence
         [ toTerm (SubHvl ntns (HVVar k2))
         , toTerm (WfTerm
                     (HVAppend (HVVar k1) (HVVar k2))
                     (SWeaken (SVar t) (HVVar k2)))
         , toTerm (WfTerm (HVVar k1) (SVar t))
         ]
        )

  proof <- sequence
    [ pure $ PrTactic "needleGenericWellformedStrengthen" []
    ]

  return $
    SentenceAssertionProof
      (Assertion AssLemma strengthen [] assertion)
      (ProofQed proof)
