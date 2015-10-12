
module KnotCore.Elaboration.Lemma.SubstShiftReflection where

import Control.Applicative

import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core

lemmas :: Elab m => [SortGroupDecl] -> m [Sentence]
lemmas sdgs = concat <$>
  sequence
    [ mapM (sortDecl ntn) sds
    | SortGroupDecl _ sds ntns _ <- sdgs,
      ntn <- ntns
    ]

sortDecl :: Elab m => NamespaceTypeName -> SortDecl -> m Sentence
sortDecl ntn (SortDecl congStn _ _) = localNames $ do

  (subStn,_) <- getNamespaceCtor ntn
  s          <- freshSubtreeVar subStn
  t          <- freshSubtreeVar congStn

  let left    = SSubst (T0 ntn) (SVar s) (SShift (C0 ntn) (SVar t))
      right   = SVar t

  assertion <-
    TermForall
      <$> sequence [toBinder s]
      <*> (TermEq <$> toTerm left <*> toTerm right)

  definition <-
    Definition
    <$> idLemmaSubstShiftReflection ntn congStn
    <*> sequence [toBinder t]
    <*> pure (Just assertion)
    <*> (TermApp
         <$> (idLemmaSubstShiftReflectionInd ntn congStn >>= toRef)
         <*> sequence [toRef t, toTerm HV0]
        )

  return $ SentenceDefinition definition
