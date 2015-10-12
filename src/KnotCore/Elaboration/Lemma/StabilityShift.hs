
module KnotCore.Elaboration.Lemma.StabilityShift where

import Control.Applicative

import Coq.StdLib as Coq
import Coq.Syntax as Coq

import KnotCore.Syntax
import KnotCore.Elaboration.Core

lemmas :: Elab m => [FunGroupDecl] -> m Coq.Sentences
lemmas fgds = concat <$> mapM funGroupDecl fgds

funGroupDecl :: Elab m => FunGroupDecl -> m Coq.Sentences
funGroupDecl fgd = do
  deps <- getSortNamespaceDependencies (fst . head $ fgdFuns fgd)
  concat <$> sequence
    [ do
        glem  <- groupLemma ntn fgd
        let fns = [ fdName fd | (_,fds) <- fgdFuns fgd, fd <- fds ]
        ilems <- case fns of
                   [_] -> return []
                   _   -> mapM (individualLemma ntn (fgdName fgd)) fns
        return (glem:ilems)
    | ntn <- deps
    ]

individualLemma :: Elab m => NamespaceTypeName -> FunGroupName -> FunName -> m Coq.Sentence
individualLemma ntn fgn fn = do

  glem  <- idLemmaStabilityShiftGroup ntn fgn
  lem   <- idLemmaStabilityShift ntn fn
  let stn = fnSort fn
  sv    <- freshSubtreeVar stn
  ass   <- individualAssertion ntn sv fn
  proof <- sequence
           [ pure (Coq.PrIntros [])
           , Coq.PrTactic "eapply" <$> sequence [toRef glem]
           ]
  svbinder <- toBinder sv
  return $ Coq.SentenceAssertionProof
                     (Coq.Assertion Coq.AssLemma lem [svbinder] ass)
                     (Coq.ProofQed [Coq.PrSeq proof])

groupLemma :: Elab m => NamespaceTypeName -> FunGroupDecl -> m Coq.Sentence
groupLemma ntn fgd = do

  let fgn  = fgdName fgd
      sgtn = groupName [ stn | (stn,_) <- fgdFuns fgd ]

  shiftFuns  <- idLemmaStabilityShiftGroup ntn fgn
  induction  <- idFunctionInductionSortGroup fgn sgtn
  assertion <- Coq.all <$>
                  sequence
                    [ groupAssertion ntn stn fds
                    | (stn,fds) <- fgdFuns fgd
                    ]
  proof <- sequence
           [ Coq.PrTactic "apply_mutual_ind" <$> sequence [toRef induction]
           , pure Coq.PrSimpl
           , pure (Coq.PrIntros [])
           , pure (Coq.PrTactic "congruence" [])
           ]

  return $ Coq.SentenceAssertionProof
                     (Coq.Assertion Coq.AssLemma shiftFuns [] assertion)
                     (Coq.ProofQed [Coq.PrSeq proof])


groupAssertion :: Elab m => NamespaceTypeName -> SortTypeName -> [FunDecl] -> m Coq.Term
groupAssertion ntn stn fds = do

  sv <- freshSubtreeVar stn
  assertions <- Coq.all <$> sequence
                  [ individualAssertion ntn sv (fdName fd)
                  | fd <- fds
                  ]

  Coq.TermForall
    <$> sequence [toBinder sv]
    <*> pure assertions

individualAssertion :: Elab m => NamespaceTypeName -> SubtreeVar -> FunName -> m Coq.Term
individualAssertion ntn sv fn = do

  let stn = typeNameOf sv
  shift <- idFunctionShift ntn stn

  c     <- freshCutoffVar ntn

  left  <- Coq.TermApp
           <$> toRef fn
           <*> sequence
               [Coq.TermApp
                <$> toRef shift
                <*> sequence [toRef c, toRef sv]]

  right <- Coq.TermApp <$> toRef fn <*> sequence [toRef sv]

  Coq.TermForall
    <$> sequence [toBinder c]
    <*> pure (Coq.eq left right)
