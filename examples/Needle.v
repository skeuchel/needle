Require Import Coq.Program.Tactics.

Create HintDb infra discriminated.
Create HintDb interaction discriminated.
Create HintDb stability_shift.
Create HintDb stability_weaken.
Create HintDb stability_subst.
Create HintDb reflection discriminated.
Create HintDb shift_shift0 discriminated.
Create HintDb shift_subst0 discriminated.
Create HintDb subst_shift0 discriminated.
Create HintDb subst_subst0 discriminated.
Create HintDb shift_size discriminated.
Create HintDb weaken_size discriminated.
Create HintDb weaken_shift discriminated.
Create HintDb weaken_subst discriminated.
Create HintDb cong_shift0 discriminated.

Create HintDb shift discriminated.
Create HintDb lookup discriminated.
Create HintDb subst discriminated.
Create HintDb wf discriminated.
Create HintDb shift_wf discriminated.
Create HintDb subst_wf discriminated.

Ltac rewriteHyp :=
  match goal with
  | H:_ |- _ => rewrite H by solve [ auto ]
  end.

Ltac needleGenericStabilityWeaken :=
  let k := fresh in
    intro k; induction k as [|[]]; simpl; intros;
    autorewrite with interaction; congruence.

Ltac needleGenericWeakenAppend :=
  let x := fresh in
  let k1 := fresh in
  let k2 := fresh in
    intros x k1 k2; revert k1 x;
    induction k2 as [| () k2]; intros; simpl;
    auto; f_equal; auto.

Ltac needleGenericShiftIndexCommInd :=
  let k := fresh in
  intro k; induction k as [| () k];
    let x := fresh in
    intros ? x; simpl; auto;
    destruct x; simpl; f_equal; auto.

Ltac needleGenericWeakenShift :=
  let k := fresh in
    intro k; induction k as [| () k]; intros; simpl;
    autorewrite with shift_shift0;
    auto with cong_shift0.

Ltac needleGenericSubstIndexShiftIndexReflectionInd :=
  let k := fresh in
  simpl; intros k; induction k as [| () k];
   (let x := fresh in
    intros x; simpl; auto; (first
     [ rewriteHyp; auto | destruct x; simpl; auto; rewriteHyp; auto ])).

Ltac needleGenericShiftSubstIndexCommInd :=
  let k := fresh in
    intro k; induction k as [| () k];
    let x := fresh in
      intros x; simpl; auto; destruct x; simpl;
      autorewrite with shift_shift0;
      auto with cong_shift0.

Ltac needleGenericSubstSubstIndexCommInd :=
  let k := fresh in
    intro k; induction k as [| () k];
    let x := fresh in
      intros x; simpl; auto; destruct x; simpl;
      autorewrite with reflection subst_shift0;
      auto with cong_shift0.

Ltac needleGenericWeakenSubst :=
  let k := fresh in
    intro k; induction k as [| () k]; intros; simpl;
    autorewrite with subst_shift0;
    auto with cong_shift0.

Ltac needleGenericAppendEnvAssoc :=
  let d := fresh in
    intros ? ? d; induction d; simpl; congruence.

Ltac needleGenericDomainEnvAppendEnv :=
  let d := fresh in
    intros ? d; induction d; simpl; congruence.

Ltac needleGenericDomainEnvShiftEnv :=
  let d := fresh in
    intros ? d; induction d; simpl; congruence.

Ltac needleGenericDomainEnvSubstEnv :=
  let d := fresh in
    intros ? ? d; induction d; simpl; congruence.

Ltac needleGenericShiftEnvAppendEnv :=
  let c  := fresh in
  let d1 := fresh in
  let d2 := fresh in
    intros c d1 d2; revert c d1;
    induction d2; intros; simpl;
    first
      [ reflexivity
      | f_equal;
        autorewrite with
          weakencutoff_append
          env_domain_append;
        auto
      ].

Ltac needleGenericSubstEnvAppendEnv :=
  let x  := fresh in
  let s  := fresh in
  let d1 := fresh in
  let d2 := fresh in
    intros x s d1 d2; revert x s d1;
    induction d2; intros; simpl;
    first
      [ reflexivity
      | f_equal;
        autorewrite with
          weakentrace_append
          env_domain_append;
        auto
      ].

Ltac needleGenericLookupInversion :=
  inversion 1; auto.

Ltac needleGenericLookupFunctional :=
  induction 1; inversion 1; firstorder.

Ltac needleGenericInsertLookup :=
  induction 1;
  first
    [ constructor; auto; fail
    | inversion 1; subst; simpl;
      autorewrite with shift_shift0;
      constructor; eauto with shift_wf
    ].

Ltac needleGenericWeakenInsertEnv :=
  let d := fresh in
    intro d; induction d; auto; simpl; intros; constructor; auto.

Ltac needleGenericWeakenSubstEnv :=
  let d := fresh in
    intro d; induction d; auto; simpl; intros; constructor; auto.

Ltac needleGenericWeakenHVarlistInsert :=
  let k := fresh in
    intro k; induction k as [|[] k]; auto; simpl; intros; constructor; auto.

Ltac needleGenericWeakenSubstHvl :=
  let d := fresh in
    intros ? d; induction d as [|[] d]; auto; simpl; intros; constructor; auto.

Ltac needleGenericShiftWellFormedIndex :=
  induction 1; auto; simpl;
    let i:= fresh in intro i; destruct i; auto.

Ltac needleGenericLookupWellformedIndex :=
  induction 1; simpl; auto.

Ltac needleGenericInsertEnvInsertHvl :=
  induction 1; constructor; auto.

Ltac needleGenericSubstEnvSubstHvl :=
  induction 1; constructor; auto.

Ltac needleGenericSubstHvlWfIndexHom :=
  induction 1;
    let x := fresh in
      intros x ?; destruct x;
      try constructor; simpl; eauto with shift_wf.

Ltac needleGenericSubstHvlWfIndexHet :=
  induction 1;
    let x := fresh in
      intro x; simpl; auto; destruct x; simpl; auto.

Ltac needleGenericWeakenSize :=
  let k := fresh in
    intro k; induction k as [| () k]; simpl; intros;
    autorewrite with shift_size; auto.

Ltac needleGenericWeakenLookup :=
  let d:= fresh in
    intros ? d; induction d; simpl; intros; try constructor; auto.

Ltac needleGenericSubstEnvLookup :=
  induction 1; inversion 1; subst; simpl;
    autorewrite with reflection subst_shift0;
    try constructor; eauto with subst_wf.

Ltac needleGenericLookupWellformedData :=
  induction 1; destruct_conjs; eauto with shift_wf.

(* Apply mutual induction and never introduce any hypotheses. *)
Ltac apply_mutual_ind ind := first
 [ refine (ind _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
 | refine (ind _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
 | refine (ind _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
 | refine (ind _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
 | refine (ind _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
 | refine (ind _ _ _ _ _ _ _ _ _ _ _ _ _ _)
 | refine (ind _ _ _ _ _ _ _ _ _ _ _ _ _)
 | refine (ind _ _ _ _ _ _ _ _ _ _ _ _)
 | refine (ind _ _ _ _ _ _ _ _ _ _ _)
 | refine (ind _ _ _ _ _ _ _ _ _ _)
 | refine (ind _ _ _ _ _ _ _ _ _)
 | refine (ind _ _ _ _ _ _ _ _)
 | refine (ind _ _ _ _ _ _ _)
 | refine (ind _ _ _ _ _ _)
 | refine (ind _ _ _ _ _)
 | refine (ind _ _ _ _)
 | refine (ind _ _ _)
 | refine (ind _ _) ].

Ltac isimpl := intros; simpl in *; autorewrite with interaction in *.

Lemma eq_ind2 {A B: Type} (P: A -> B -> Prop)
  {a1 a2 b1 b2} (eq_a: a1 = a2) (eq_b: b1 = b2) :
  P a1 b1 -> P a2 b2.
Proof.
  subst; auto.
Qed.

Require Import Coq.Arith.Le.

Lemma sizeind {T : Set} (size: T -> nat) (P: T -> Prop)
      (step: forall u, (forall t, size t < size u -> P t) -> P u) :
  forall v, P v.
Proof.
  cut (forall n v, size v <= n -> P v); eauto.
  induction n; intros; apply step; intros t t_lt_v;
    pose proof (le_trans _ _ _ t_lt_v H) as lt_t_n.
  - destruct (le_Sn_0 _ lt_t_n).
  - exact (IHn _ (le_S_n _ _ lt_t_n)).
Qed.
