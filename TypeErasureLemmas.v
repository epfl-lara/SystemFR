Require Import Coq.Program.Tactics.

Require Export SystemFR.Syntax.
Require Export SystemFR.Tactics.
Require Export SystemFR.AssocList.
Require Export SystemFR.TypeErasure.

Require Export SystemFR.ListUtils.
Require Export SystemFR.SmallStep.
Require Export SystemFR.WFLemmas.
Require Export SystemFR.TWFLemmas.
Require Export SystemFR.RelationClosures.
Require Export SystemFR.ErasedTermLemmas.

Open Scope list_scope.

Lemma in_erased_context:
  forall (gamma : context) (x : nat) (T : tree) eq,
    lookup eq gamma x = Some T ->
    lookup eq (erase_context gamma) x = Some (erase_type T).
Proof.
  induction gamma; steps.
Qed.

Lemma erased_context_support:
  forall l, support (erase_context l) = support l.
Proof.
  induction l; steps.
Qed.

Lemma erase_context_append:
  forall l1 l2,
    erase_context (l1 ++ l2) = erase_context l1 ++ erase_context l2.
Proof.
  induction l1; steps.
Qed.

Lemma erase_term_term_var:
  forall t x,
    x ∈ pfv (erase_term t) term_var ->
    x ∈ pfv t term_var.
Proof.
  induction t; repeat step || t_listutils.
Qed.

Hint Immediate erase_term_term_var: fv.

Lemma erase_term_type_var:
  forall t x,
    x ∈ pfv (erase_term t) type_var ->
    False.
Proof.
  induction t; repeat step || t_listutils; eauto.
Qed.

Hint Immediate erase_term_type_var: fv.

Lemma erase_term_var:
  forall t x tag,
    x ∈ pfv (erase_term t) tag ->
    x ∈ pfv t tag.
Proof.
  destruct tag; intros; eauto with fv exfalso.
Qed.

Hint Immediate erase_term_var: fv.

Lemma erase_type_var:
  forall t x tag,
    x ∈ pfv (erase_type t) tag ->
    x ∈ pfv t tag.
Proof.
  induction t; destruct tag; repeat step || t_listutils;
    eauto using erase_term_term_var, erase_term_type_var with exfalso.
Qed.

Hint Immediate erase_type_var: fv.

Lemma erase_context_var:
  forall gamma x tag,
    x ∈ pfv_context (erase_context gamma) tag ->
    x ∈ pfv_context gamma tag.
Proof.
  induction gamma; repeat step || t_listutils; eauto with fv.
Qed.

Hint Immediate erase_context_var: fv.

Ltac t_fv_erase :=
  match goal with
  | H: _ ∈ pfv_context (erase_context _) _ |- _ => apply erase_context_var in H
  | H: _ ∈ pfv (erase_term _) _ |- _ => apply erase_term_var in H
  | H: _ ∈ pfv (erase_type _) _ |- _ => apply erase_type_var in H
  end.

Lemma erase_term_wf:
  forall t k,
    wf t k ->
    wf (erase_term t) k.
Proof.
  induction t; steps.
Qed.

Hint Resolve erase_term_wf: wf.

Lemma erase_type_wf:
  forall T k,
    wf T k ->
    wf (erase_type T) k.
Proof.
  induction T; steps; eauto using erase_term_wf.
Qed.

Hint Resolve erase_type_wf: wf.

Lemma erase_term_twf:
  forall t k,
    twf (erase_term t) k.
Proof.
  induction t; steps.
Qed.

Hint Resolve erase_term_twf: btwf.

Lemma erase_type_twf:
  forall T k,
    twf T k ->
    twf (erase_type T) k.
Proof.
  induction T; steps; eauto using erase_term_twf.
Qed.

Hint Resolve erase_type_twf: btwf.

Lemma pfv_erase_context_subst:
  forall S gamma tag,
    subset (pfv_context gamma tag) S ->
    subset (pfv_context (erase_context gamma) tag) S.
Proof.
  unfold subset; steps; eauto with fv.
Qed.

Lemma pfv_erase_term_subst:
  forall S t tag,
    subset (pfv t tag) S ->
    subset (pfv (erase_term t) tag) S.
Proof.
  unfold subset; destruct tag; steps; eauto with fv exfalso.
Qed.

Lemma pfv_erase_type_subst:
  forall S T tag,
    subset (pfv T tag) S ->
    subset (pfv (erase_type T) tag) S.
Proof.
  unfold subset; steps; eauto with fv.
Qed.

Ltac t_subset_erase :=
  apply pfv_erase_context_subst ||
  apply pfv_erase_term_subst ||
  apply pfv_erase_type_subst.

Lemma erase_term_open:
  forall t1 t2 k,
    is_annotated_term t1 ->
    erase_term (open k t1 t2) = open k (erase_term t1) (erase_term t2).
Proof.
  induction t1;
    try solve [ repeat step || t_equality ].
Qed.

Lemma erase_type_open:
  forall T t k,
    is_annotated_type T ->
    is_annotated_term t ->
    erase_type (open k T t) = open k (erase_type T) (erase_term t).
Proof.
  induction T; try destruct f;
    try solve [ repeat step || rewrite erase_term_open in * || t_equality ].
Qed.

Lemma erase_term_topen:
  forall t1 t2 k,
    is_annotated_term t1 ->
    erase_term (topen k t1 t2) = erase_term t1.
Proof.
  induction t1;
    try solve [ repeat step || t_equality ].
Qed.

Lemma topen_erase_term:
  forall t1 t2 k,
    topen k (erase_term t1) t2 = erase_term t1.
Proof.
  intros; rewrite topen_none; steps;
    eauto using is_erased_term_twf, erase_term_erased with btwf.
Qed.

Lemma erase_type_topen:
  forall T1 T2 k,
    is_annotated_type T1 ->
    is_annotated_type T2 ->
    erase_type (topen k T1 T2) = topen k (erase_type T1) (erase_type T2).
Proof.
  induction T1;
    repeat step || rewrite erase_term_topen in * || t_equality || rewrite topen_erase_term in *.
Qed.
