Require Import SystemFR.Syntax.
Require Import SystemFR.Sets.
Require Import SystemFR.Tactics.
Require Import SystemFR.SmallStep.
Require Import SystemFR.AssocList.
Require Import SystemFR.ErasedTermLemmas.


Require Import PeanoNat.

Open Scope list_scope.

Definition reducibility_candidate (P: tree -> Prop): Prop :=
  forall v, P v ->
       is_erased_term v /\
       is_value v /\
       wf v 0 /\
       pfv v term_var = nil.

(* an interpretation for every type variable, as a reducibility candidate *)
Definition interpretation: Type := list (nat * (tree -> Prop)).

Definition pre_interpretation: Type := list (nat * (tree -> tree -> Prop)).

Fixpoint valid_interpretation (theta: interpretation): Prop :=
  match theta with
  | nil => True
  | (x,P) :: theta' => valid_interpretation theta' /\ reducibility_candidate P
  end.

Lemma valid_interpretation_cons:
  forall theta RC X,
    valid_interpretation theta ->
    reducibility_candidate RC ->
    valid_interpretation ((X, RC) :: theta).
Proof.
  steps.
Qed.

Lemma in_valid_interpretation_erased: forall theta v X P,
  valid_interpretation theta ->
  lookup Nat.eq_dec theta X = Some P ->
  P v ->
  is_erased_term v.
Proof.
  induction theta; repeat step || eauto || apply_any.
Qed.

Lemma in_valid_interpretation_wf: forall theta v X P,
  valid_interpretation theta ->
  lookup Nat.eq_dec theta X = Some P ->
  P v ->
  wf v 0.
Proof.
  induction theta; repeat step || eauto || apply_any.
Qed.

Lemma in_valid_interpretation_value: forall theta v X P,
  valid_interpretation theta ->
  lookup Nat.eq_dec theta X = Some P ->
  P v ->
  is_value v.
Proof.
  induction theta; repeat step || eauto || apply_any.
Qed.

Lemma in_valid_interpretation_fv: forall theta v X P,
  valid_interpretation theta ->
  lookup Nat.eq_dec theta X = Some P ->
  P v ->
  pfv v term_var = nil.
Proof.
  induction theta; repeat step || eauto || apply_any.
Qed.

Lemma in_valid_interpretation_tfv: forall theta v X P,
  valid_interpretation theta ->
  lookup Nat.eq_dec theta X = Some P ->
  P v ->
  pfv v type_var = nil.
Proof.
  intros; eauto using is_erased_term_tfv, in_valid_interpretation_erased.
Qed.

Lemma in_valid_interpretation_pfv: forall theta v X P tag,
  valid_interpretation theta ->
  lookup Nat.eq_dec theta X = Some P ->
  P v ->
  pfv v tag = nil.
Proof.
  destruct tag; eauto using in_valid_interpretation_fv, in_valid_interpretation_tfv.
Qed.

Lemma in_valid_interpretation_twf: forall theta v X P,
  valid_interpretation theta ->
  lookup Nat.eq_dec theta X = Some P ->
  P v ->
  twf v 0.
Proof.
  eauto using is_erased_term_twf, in_valid_interpretation_erased.
Qed.

Fixpoint valid_pre_interpretation (P: tree -> Prop) (theta: list (nat * (tree -> tree -> Prop))) : Prop :=
  match theta with
  | nil => True
  | (_, RC) :: theta' => valid_pre_interpretation P theta' /\ forall a, P a -> reducibility_candidate (RC a)
  end.

Lemma valid_interpretation_equiv:
  forall P1 P2 ptheta,
    valid_pre_interpretation P1 ptheta ->
    (forall x, P1 x <-> P2 x) ->
    valid_pre_interpretation P2 ptheta.
Proof.
  induction ptheta; steps; eauto with beapply_any.
Qed.

Ltac t_valid_interpretation_equiv :=
  match goal with
  | H1: valid_pre_interpretation ?P1 ?ptheta |- valid_pre_interpretation _ ?ptheta => apply valid_interpretation_equiv with P1
  end.

Definition push_one (a: tree) (l: list (nat * (tree -> tree -> Prop))): interpretation :=
  mapValues (fun rc => rc a) l.
Definition push_all (P: tree -> Prop) (l: list (nat * (tree -> tree -> Prop))): interpretation :=
  mapValues (fun (rc: tree -> tree -> Prop) (v: tree) => (forall a, P a -> rc a v)) l.

Lemma valid_interpretation_one:
  forall a (P: tree -> Prop) theta,
    P a ->
    valid_pre_interpretation P theta ->
    valid_interpretation (push_one a theta).
Proof.
  induction theta; steps.
Qed.

Lemma valid_interpretation_append:
  forall theta1 theta2,
    valid_interpretation theta1 ->
    valid_interpretation theta2 ->
    valid_interpretation (theta1 ++ theta2).
Proof.
  induction theta1; steps.
Qed.

Hint Resolve valid_interpretation_cons: b_valid_interp.
Hint Resolve valid_interpretation_one: b_valid_interp.

Hint Resolve valid_interpretation_append: b_valid_interp.
Hint Extern 1 => eapply valid_interpretation_one; eauto: b_valid_interp.
