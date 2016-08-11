
module KnotCore.Elaboration.Namespace where

import Control.Applicative
import Control.Monad

import Coq.Syntax
import Coq.StdLib

import KnotCore.Syntax
import KnotCore.Elaboration.Core

eNamespace :: Elab m => [NamespaceDecl] -> m Sentences
eNamespace nds = sequenceA
  [ eTypeNamespace nds,
    eEqNamespaceDec nds
  ]

eTypeNamespace :: Elab m => [NamespaceDecl] -> m Sentence
eTypeNamespace nds =
  SentenceInductive . Inductive <$> sequenceA
    [ InductiveBody
      <$> idTypeNamespace
      <*> pure []
      <*> pure (TermSort Type)
      <*> for nds (\nd ->
            InductiveCtor
            <$> idCtorNamespace (typeNameOf nd)
            <*> pure []
            <*> pure Nothing
          )
    ]

eEqNamespaceDec :: Elab m => [NamespaceDecl] -> m Sentence
eEqNamespaceDec _ = localNames $ do

  lem       <- idLemmaEqNamespaceDec

  namespace <- idTypeNamespace
  a         <- freshVariable "a" =<< toRef namespace
  b         <- freshVariable "b" =<< toRef namespace
  binders   <- sequenceA [toBinder a, toBinder b]
  eq_ab     <- eq <$> toRef a <*> toRef b

  let assertion = sumbool eq_ab (Coq.StdLib.not eq_ab)
      proof = [PrTactic "decide equality" []]

  return $
    SentenceAssertionProof
      (Assertion AssLemma lem binders assertion)
      (ProofDefined proof)
