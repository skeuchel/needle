
module KnotCore.Elaboration.Lemma.ShiftSubstComm where

import Control.Applicative

import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core

lemmas :: Elab m => [SortGroupDecl] -> m [Sentence]
lemmas sdgs = concat <$>
  sequence
    [ mapM (sortDecl ntna ntnb) sds
    | SortGroupDecl _ sds ntns _ <- sdgs,
      ntna <- ntns,
      ntnb <- ntns
    ]

sortDecl :: Elab m => NamespaceTypeName -> NamespaceTypeName -> SortDecl -> m Sentence
sortDecl ntna ntnb (SortDecl stn _ _) = localNames $ do

  (stnb,_) <- getNamespaceCtor ntnb
  depsb    <- getSortNamespaceDependencies stnb

  ca      <- freshCutoffVar ntna
  tb      <- freshSubtreeVar stnb
  t       <- freshSubtreeVar stn

  let left   = SShift (CVar ca) (SSubst (T0 ntnb) (SVar tb) (SVar t))
      -- α ≡ β
      right1 = SSubst (T0 ntnb)
                 (SShift (CVar ca) (SVar tb))
                 (SShift (CS (CVar ca)) (SVar t))
      -- α ≢ β, α ∈ β
      right2 = SSubst (T0 ntnb)
                 (SShift (CVar ca) (SVar tb))
                 (SShift (CVar ca) (SVar t))
      -- α ≢ β, α ∉ β.
      right3 = SSubst (T0 ntnb)
                 (SVar tb)
                 (SShift (CVar ca) (SVar t))
      right | ntna == ntnb      = right1
            | ntna `elem` depsb = right2
            | otherwise         = right3

  assertion <-
    TermForall
      <$> sequence [toBinder ca, toBinder tb]
      <*> (TermEq <$> toTerm left <*> toTerm right)

  definition <-
    Definition
    <$> idLemmaShiftSubstComm ntna ntnb stn
    <*> sequence [toBinder t]
    <*> pure (Just assertion)
    <*> (TermApp
         <$> (idLemmaShiftSubstCommInd ntna ntnb stn >>= toRef)
         <*> sequence [toRef t, toTerm HV0]
        )

  return $ SentenceDefinition definition
