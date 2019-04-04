Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Require Import SystemFR.Syntax.
Require Import SystemFR.Tactics.
Require Import SystemFR.SmallStep.
Require Import SystemFR.SubstitutionLemmas.
Require Import SystemFR.AssocList.

Fixpoint are_values (l: list (nat * tree)) :=
  match l with
  | nil => True
  | (x,v) :: l' => is_value v /\ are_values l'
  end.

Lemma lookup_value:
  forall l, are_values l ->
       forall x t, lookup Nat.eq_dec l x = Some t ->
              is_value t.
Proof.
  induction l; steps; eauto.
Qed.

Lemma is_value_subst:
  forall v,
    is_value v ->
    forall l,
      are_values l ->
      is_value (substitute v l).
Proof.
  induction 1; steps; eauto with values; eauto using lookup_value.
Qed.

Hint Resolve is_value_subst: values.

(* Not true anymore when introducing a size primitive
Lemma small_step_subst:
  forall t t' l,
    small_step t t' ->
    are_values l ->
    wfs l 0 ->
    small_step (substitute t l) (substitute t' l).
Proof.
  induction 1; steps; eauto using is_value_subst with values smallstep;
    repeat rewrite substitute_open; steps; eauto using is_value_subst with smallstep bwf.
Qed.

Ltac t_smallstep_subst :=
  match goal with
  | H: small_step ?t1 ?t2, l: list (nat * tree) |- _ =>
    is_var t1; is_var t2;
    poseNew (Mark (t1,t2,l) "small_step_subst");
    unshelve epose proof (small_step_subst t1 t2 l H _ _)
  end.
*)