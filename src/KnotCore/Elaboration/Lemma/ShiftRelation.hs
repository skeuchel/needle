
module KnotCore.Elaboration.Lemma.ShiftRelation where

import Control.Applicative
import Control.Monad
import Data.Maybe

import qualified Coq.StdLib as Coq
import qualified Coq.Syntax as Coq

import KnotCore.Syntax
import KnotCore.Elaboration.Core
import KnotCore.Elaboration.LookupRelation
import KnotCore.Elaboration.InsertionRelation

lemmasShiftLookupRelation :: Elab m => RelationDecl -> m Coq.Sentences
lemmasShiftLookupRelation ed = undefined
  -- do
  --   lks <- mkLookupRelations ed
  --   iss <- mkInsertRelations ed
  --   sequence [ lemmaShiftLookupRelation is lk | is <- iss, lk <- lks ]

lemmaShiftLookupRelation :: Elab m =>
                            InsertRelation ->
                            RelationDecl ->
                            m Coq.Sentence
lemmaShiftLookupRelation
    (InsertRelation rtn ntn etn here theres)
    (RelationDecl (Just envName) rtn' stns' rules') =
    do
      co      <- freshCutoff ntn
      en1     <- freshEnvName etn
      en2     <- freshEnvName etn
      indices <- mapM freshSubtreeName stns
      let jdg = Judgement rtn' (SymEnv en1 : map SymSubtree indices)
      hy      <- freshHypothesis (NR "H") Nothing (FormJudgement [] jdg)

      assertion <- Coq.Assertion Coq.AssLemma
                     <$> lemmaShiftRelationIdentifier rtn rtn'
                     <*> sequence ( envNameBinder en1 :
                                    map subtreeBinder indices ++
                                    hypothesisBinder hy
                                  )
                     <*> (Coq.TermForall
                          <$> sequence (cutoffBinder co :
                                        envNameBinder en2 :

                                        map subtreeBinder lkIndices)
                          <*> (Coq.TermFunction
                                 <$> (Coq.TermApp
                                        <$> relationType rtn'
                                        <*> sequence
                                            (envNameRef en1 :
                                             metavarRef lkMetavar :
                                             map subtreeRef lkIndices)
                                      )
                                 <*> (Coq.TermApp
                                        <$> relationType rtn'
                                        <*> sequence
                                            (envNameRef en2 :
                                             shiftedMetavarRef co lkMetavar :
                                             map (shiftedSubtreeRef co) lkIndices)
                                     )
                              )
                         )

{-

      proof     <- fmap (Coq.ProofQed . (:[]) . Coq.PrSeq) $
                     do
                       insRef <- hypothesisIdentifier hy
                       return
                         [ Coq.PrInduction insRef,
                           Coq.PrIntros,
                           Coq.PrTry (Coq.PrSeq
                                        [ Coq.PrConstructor,
                                          Coq.PrAuto,
                                          Coq.PrFail
                                        ]),
                           Coq.PrInversion (Coq.ID "H"),
                           Coq.PrSubst,
                           Coq.PrSimpl,
                           Coq.PrTry Coq.PrRewriter,
                           Coq.PrConstructor,
                           Coq.PrAuto
                         ]
      return $ Coq.SentenceAssertionProof assertion proof
-}


{-
Section ShiftRelationLemmas.
  Lemma shiftSub :
    (forall (E : Env) (T1 : Ty) (T2 : Ty) (Sub0 : Sub E T1 T2) c0 (E0 : Env),
       (Insert_evar c0 E E0) -> Sub E0 T1 T2).
  Proof.
    congruence_Jsub
      (simpl; intros; specialize_insert; rewriter)
      (simpl; eauto with constr shift).
  Qed.
  Hint Resolve shiftSub.
  Lemma tshiftSub :
    (forall (E : Env) (T1 : Ty) (T2 : Ty) (Sub0 : Sub E T1 T2) c0 (E0 : Env),
       (Insert_ebound c0 E E0) -> Sub E0 (tshiftTy (c0) T1) (tshiftTy (c0) T2)).
  Proof.
    congruence_Jsub
      (simpl; intros; specialize_insert; rewriter)
      (simpl; eauto with constr shift).
  Qed.
  Hint Resolve tshiftSub.

End ShiftRelationLemmas.
-}
