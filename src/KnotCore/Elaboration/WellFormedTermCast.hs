
module KnotCore.Elaboration.WellFormedTermCast where

import           Coq.StdLib
import           Coq.Syntax

import           KnotCore.DeBruijn.Core
import           KnotCore.Elaboration.Core
import           KnotCore.Elaboration.Fresh

import           Control.Monad
import           Data.Maybe
import           Data.Traversable (Traversable(..))

lemmas :: Elab m => [SortGroupDecl] -> m [Sentence]
lemmas = traverse eSortDecl . concatMap sgSorts

mkEq :: (Elab m, Ident a) => a -> a -> m Term
mkEq x y = TermEq <$> toRef x <*> toRef y

eSortDecl :: Elab m => SortDecl -> m Sentence
eSortDecl sd = localNames $ do

  let stn = typeNameOf sd
  h1 <- freshHVarlistVar
  h2 <- freshHVarlistVar
  sv1 <- freshSortVariable stn
  sv2 <- freshSortVariable stn

  lem <- idLemmaWellFormedTermCast stn

  binders <-
    sequence
      [ toBinder h1
      , toBinder sv1
      , toBinder h2
      , toBinder sv2
      ]

  eqs <- sequenceA
    [ mkEq h1 h2
    , mkEq sv1 sv2
    ]

  wf1 <- toTerm (WfSort (HVVar h1) (SVar sv1))
  wf2 <- toTerm (WfSort (HVVar h2) (SVar sv2))

  let statement :: Term
      statement = TermForall binders (foldl1 TermFunction (eqs ++ [wf1, wf2]))

      assertion :: Assertion
      assertion = Assertion AssLemma lem [] statement

      proof :: Proof
      proof = ProofQed [PrTactic "congruence" []]

  return $ SentenceAssertionProof assertion proof
