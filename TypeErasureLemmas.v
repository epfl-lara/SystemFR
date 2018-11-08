Require Import Coq.Program.Tactics.

Require Import Termination.Syntax.
Require Import Termination.TermForm.
Require Import Termination.Tactics.
Require Import Termination.AssocList.
Require Import Termination.TypeErasure.
Require Import Termination.Sets.
Require Import Termination.ListUtils.
Require Import Termination.SmallStep.

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

Hint Rewrite erased_context_support: berased.

Lemma erase_context_append:
  forall l1 l2,
    erase_context (l1 ++ l2) = erase_context l1 ++ erase_context l2.
Proof.
  induction l1; steps.
Qed.

Hint Rewrite erase_context_append: berased.

Lemma erase_term_term_var:
  forall t x,
    x ∈ pfv (erase_term t) term_var ->
    x ∈ pfv t term_var.
Proof.
  induction t; repeat step || t_listutils.
Qed.

Hint Immediate erase_term_term_var: bfv.

Lemma erase_term_type_var:
  forall t x,
    x ∈ pfv (erase_term t) type_var ->
    False.
Proof.
  induction t; repeat step || t_listutils; eauto.
Qed.

Hint Immediate erase_term_type_var: bfv.

Lemma erase_term_var:
  forall t x tag,
    x ∈ pfv (erase_term t) tag ->
    x ∈ pfv t tag.
Proof.
  destruct tag; intros; eauto with bfv falsity.
Qed.

Hint Immediate erase_term_var: bfv.

Lemma erase_type_var:
  forall t x tag,
    x ∈ pfv (erase_type t) tag ->
    x ∈ pfv t tag.
Proof.
  induction t; destruct tag; repeat step || t_listutils;
    eauto using erase_term_term_var, erase_term_type_var with falsity.
Qed.

Hint Immediate erase_type_var: bfv.

Lemma erase_context_var:
  forall gamma x tag,
    x ∈ pfv_context (erase_context gamma) tag ->
    x ∈ pfv_context gamma tag.
Proof.
  induction gamma; repeat step || t_listutils; eauto with bfv.
Qed.

Hint Immediate erase_context_var: bfv.

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

Hint Resolve erase_term_wf: bwf.

Lemma erase_type_wf:
  forall T k,
    wf T k ->
    wf (erase_type T) k.
Proof.
  induction T; steps; eauto using erase_term_wf.
Qed.

Hint Resolve erase_type_wf: bwf.

Lemma pfv_erase_context_subst:
  forall S gamma tag,
    subset (pfv_context gamma tag) S ->
    subset (pfv_context (erase_context gamma) tag) S.
Proof.
  unfold subset; steps; eauto with bfv.
Qed.

Lemma pfv_erase_term_subst:
  forall S t tag,
    subset (pfv t tag) S ->
    subset (pfv (erase_term t) tag) S.
Proof.
  unfold subset; destruct tag; steps; eauto with bfv falsity.
Qed.

Lemma pfv_erase_type_subst:
  forall S T tag,
    subset (pfv T tag) S ->
    subset (pfv (erase_type T) tag) S.
Proof.
  unfold subset; steps; eauto with bfv.
Qed.

Ltac t_subset_erase :=
  apply pfv_erase_context_subst ||
  apply pfv_erase_term_subst ||
  apply pfv_erase_type_subst.

Lemma erase_term_open:
  forall t1 t2 k,
    erase_term (open k t1 t2) = open k (erase_term t1) (erase_term t2).
Proof.
  induction t1; steps.
Qed.

Hint Rewrite erase_term_open: berased.

Lemma erase_type_open:
  forall T t k,
    is_annotated_type T ->
    erase_type (open k T t) = open k (erase_type T) (erase_term t).
Proof.
  induction T;
    try solve [ repeat step || rewrite erase_term_open in * || tequality ].
Qed.

Lemma is_erased_open:
  forall t k rep,
    is_erased_term t ->
    is_erased_term rep ->
    is_erased_term (open k t rep).
Proof.
  induction t; steps.
Qed.

Hint Resolve is_erased_open: berased.

Lemma is_erased_open2:
  forall t k rep,
    is_erased_term (open k t rep) ->
    is_erased_term t.
Proof.
  induction t; steps; eauto.
Qed.

Lemma erase_smallstep:
  forall t1 t2,
    small_step t1 t2 ->
    is_erased_term t1 ->
    is_erased_term t2.
Proof.
  induction 1; steps; eauto 3 using is_erased_open with step_tactic.
Qed.

Hint Resolve erase_smallstep: berased.

Lemma is_erased_term_tfv:
  forall t,
    is_erased_term t ->
    pfv t type_var = nil.
Proof.
  induction t; repeat step || t_listutils.
Qed.

Hint Resolve is_erased_term_tfv: bfv.

(*
Lemma erase_erased:
  forall t,
    is_erased_term t ->
    t = erase_term t.
Proof.
  induction t; steps.
*)