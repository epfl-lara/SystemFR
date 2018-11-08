Require Import Termination.Syntax.
Require Import Termination.Sets.
Require Import Termination.Tactics.
Require Import Termination.SmallStep.
Require Import Termination.AssocList.

Require Import PeanoNat.

Open Scope list_scope.

Definition reducibility_candidate (P: tree -> Prop): Prop :=
  forall v, P v ->
       is_erased_term v /\
       is_value v /\
       wf v 0 /\
       pfv v term_var = nil /\
       pfv v type_var = nil.

(* an interpretation for every type variable, as a reducibility candidate *)
Definition interpretation: Type := list (nat * (tree -> Prop)).

Fixpoint valid_interpretation (theta: interpretation): Prop :=
  match theta with
  | nil => True
  | (x,P) :: theta' => valid_interpretation theta' /\ reducibility_candidate P
  end.

Lemma in_valid_interpretation_closed: forall theta v X P,
  valid_interpretation theta ->
  lookup Nat.eq_dec theta X = Some P ->
  P v ->
  (is_value v /\ wf v 0 /\ pfv v term_var = nil).
Proof.
  induction theta as [ | p theta' IH ]; repeat unfold reducibility_candidate in * || step;
    eauto;
    try solve [ apply_any; steps ];
    try solve [ eapply IH; steps; eauto ].
Qed.

Lemma in_valid_interpretation_fv: forall theta v X P tag,
  valid_interpretation theta ->
  lookup Nat.eq_dec theta X = Some P ->
  P v ->
  pfv v tag = nil.
Proof.
  induction theta; destruct tag; repeat step || eauto || apply_any.
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

Lemma in_valid_interpretation_erased: forall theta v X P,
  valid_interpretation theta ->
  lookup Nat.eq_dec theta X = Some P ->
  P v ->
  is_erased_term v.
Proof.
  induction theta; repeat step || eauto || apply_any.
Qed.
