
module KnotCore.Elaboration.Lemma.WeakenSize where

import Control.Applicative
import Data.Maybe

import Coq.StdLib
import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core
import KnotCore.Elaboration.Eq
import KnotCore.Elaboration.Lemma.Mutual

lemmas :: Elab m => m [Sentence]
lemmas = getSorts >>= mapM sortDecl

sortDecl :: Elab m => SortTypeName -> m Sentence
sortDecl stn = localNames $ do

  lemma <- idLemmaWeakenSize stn
  size  <- idFunctionSize stn
  t     <- freshSubtreeVar stn
  h     <- freshHVarlistVar

  statement <-
    TermForall
    <$> sequence [toBinder h, toBinder t]
    <*> (eq
         <$> (TermApp
              <$> toRef size
              <*> sequence [ toTerm (SWeaken (SVar t) (HVVar h)) ]
             )
         <*> (TermApp
              <$> toRef size
              <*> sequence [ toTerm (SVar t) ]
             )
        )

  return $
    SentenceAssertionProof
      (Assertion AssLemma lemma [] statement)
      (ProofQed [PrTactic "needleGenericWeakenSize" []])
