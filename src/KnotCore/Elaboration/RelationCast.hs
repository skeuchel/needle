
module KnotCore.Elaboration.RelationCast where

import           Coq.StdLib
import           Coq.Syntax

import           KnotCore.Elaboration.Core
import           KnotCore.Elaboration.Fresh

import           Control.Monad
import           Data.Maybe
import           Data.Traversable (Traversable(..))

lemmas :: Elab m => [RelationGroupDecl] -> m [Sentence]
lemmas = traverse eRelationDecl . concatMap rgRelations

toJmEnv :: Maybe EnvVariable -> JudgementEnv
toJmEnv (Just ev) = JudgementEnvTerm (EVar ev)
toJmEnv Nothing   = JudgementEnvNothing

mkEq :: (Elab m, Ident a) => a -> a -> m Term
mkEq x y = TermEq <$> toRef x <*> toRef y

eRelationDecl :: Elab m => RelationDecl -> m Sentence
eRelationDecl (RelationDecl mbEv rtn fds _roots outputs _rules) = localNames $ do

  mbEv1 <- traverse freshen mbEv
  mbEv2 <- traverse freshen mbEv
  fds1 <- freshen fds
  fds2 <- freshen fds
  fs1 <- eFieldDeclFields fds1
  fs2 <- eFieldDeclFields fds2
  fsi1 <- sequenceA (eFieldDeclIdentifiers fds1)
  fsi2 <- sequenceA (eFieldDeclIdentifiers fds2)
  outEvs1 <- traverse (freshEnvVariable . snd) outputs
  outEvs2 <- traverse (freshEnvVariable . snd) outputs

  lem <- idLemmaRelationCast rtn

  binders <-
    concat <$> sequence
      [ traverse toBinder (maybeToList mbEv1)
      , sequenceA (eFieldDeclBinders fds1)
      , traverse toBinder outEvs1
      , traverse toBinder (maybeToList mbEv2)
      , sequenceA (eFieldDeclBinders fds2)
      , traverse toBinder outEvs2
      ]

  eqs <- concat <$> sequence
    [ zipWithM mkEq (maybeToList mbEv1) (maybeToList mbEv2)
    , zipWithM mkEq fsi1 fsi2
    , zipWithM mkEq outEvs1 outEvs2
    ]

  jmt1 <- toTerm (PJudgement rtn (toJmEnv mbEv1) fs1 (map EVar outEvs1))
  jmt2 <- toTerm (PJudgement rtn (toJmEnv mbEv2) fs2 (map EVar outEvs2))

  let statement :: Term
      statement = TermForall binders (foldl1 TermFunction (eqs ++ [jmt1, jmt2]))

      assertion :: Assertion
      assertion = Assertion AssLemma lem [] statement

      proof :: Proof
      proof = ProofQed [PrTactic "congruence" []]

  return $ SentenceAssertionProof assertion proof
