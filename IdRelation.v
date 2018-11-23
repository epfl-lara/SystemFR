Require Import Termination.Syntax.
Require Import Termination.Sets.
Require Import Termination.Tactics.
Require Import Termination.SetLemmas.
Require Import Termination.AssocList.
Require Import Termination.ListUtils.
Require Import Termination.EqualWithRelation.
Require Import Termination.EquivalentWithRelation.

Require Import PeanoNat.

Open Scope list_scope.

Fixpoint idrel (l: list nat) :=
  match l with
  | nil => nil
  | x :: xs => (x,x) :: idrel xs
  end.

Lemma idrel_lookup:
  forall l x,
    x ∈ l ->
    lookup Nat.eq_dec (idrel l) x = Some x.
Proof.
  induction l; steps.
Qed.

Lemma idrel_lookup_swap:
  forall l x,
    x ∈ l ->
    lookup Nat.eq_dec (swap (idrel l)) x = Some x.
Proof.
  induction l; steps.
Qed.

Lemma equal_with_idrel:
  forall t, equal_with_relation (idrel (pfv t type_var)) t t.
Proof.
  intros; apply equal_with_relation_refl2; steps;
    eauto using idrel_lookup, idrel_lookup_swap.
Qed.

Lemma idrel_lookup_fail:
  forall l x,
    (x ∈ l -> False) ->
    lookup Nat.eq_dec (idrel l) x = None.
Proof.
  induction l; steps.
Qed.

Lemma idrel_lookup_swap_fail:
  forall l x,
    (x ∈ l -> False) ->
    lookup Nat.eq_dec (swap (idrel l)) x = None.
Proof.
  induction l; steps.
Qed.

Lemma support_idrel:
  forall l, support (idrel l) = l.
Proof.
  induction l; steps.
Qed.

Lemma range_idrel:
  forall l, range (idrel l) = l.
Proof.
  induction l; steps.
Qed.

Lemma support_swap:
  forall l, support (swap l) = range l.
Proof.
  induction l; steps.
Qed.

Lemma range_swap:
  forall l, range (swap l) = support l.
Proof.
  induction l; steps.
Qed.

Lemma equivalent_rc_refl:
  forall rc, equivalent_rc rc rc.
Proof.
  unfold equivalent_rc; steps.
Qed.

Lemma equivalent_rc_at_right:
  forall x y theta t,
    x <> y ->
    equivalent_rc_at theta ((x,t) :: theta) y y.
Proof.
  unfold equivalent_rc_at; steps; eauto using equivalent_rc_refl.
Qed.

Lemma equivalent_with_idrel:
  forall l x theta t,
    (x ∈ l -> False) ->
    equivalent_with_relation (idrel l) theta ((x,t) :: theta).
Proof.
  unfold equivalent_with_relation;
    repeat step || t_lookup ||
           rewrite support_idrel in * ||
           rewrite support_swap in * ||
           rewrite range_idrel in * ||
           rewrite range_swap in * ||
           (rewrite idrel_lookup in * by auto) ||
           (rewrite idrel_lookup_swap_fail in * by auto) ||
           apply equivalent_rc_at_right.
Qed.

Lemma equivalent_rc_at_left:
  forall x y theta t,
    x <> y ->
    equivalent_rc_at ((x,t) :: theta) theta y y.
Proof.
  unfold equivalent_rc_at; steps; eauto using equivalent_rc_refl.
Qed.

Lemma equivalent_with_idrel2:
  forall l x theta t,
    (x ∈ l -> False) ->
    equivalent_with_relation (idrel l) ((x,t) :: theta) theta.
Proof.
  unfold equivalent_with_relation;
    repeat step || t_lookup ||
           rewrite support_idrel in * ||
           rewrite support_swap in * ||
           rewrite range_idrel in * ||
           rewrite range_swap in * ||
           (rewrite idrel_lookup in * by auto) ||
           (rewrite idrel_lookup_swap_fail in * by auto) ||
           apply equivalent_rc_at_left.
Qed.

Ltac t_idrel :=
  rewrite support_idrel in * ||
  rewrite support_swap in * ||
  rewrite range_idrel in * ||
  rewrite range_swap in * ||
  (rewrite idrel_lookup in * by auto) ||
  (rewrite idrel_lookup_swap_fail in * by auto).
