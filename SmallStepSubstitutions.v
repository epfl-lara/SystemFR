Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Require Export SystemFR.SubstitutionLemmas.
Require Export SystemFR.FVLemmasEval.

Fixpoint are_values (l: list (nat * tree)) :=
  match l with
  | nil => True
  | (x,v) :: l' => cbv_value v /\ are_values l'
  end.

Lemma lookup_value:
  forall l, are_values l ->
       forall x t, lookup Nat.eq_dec l x = Some t ->
              cbv_value t.
Proof.
  induction l; steps; eauto.
Qed.

Lemma cbv_value_subst:
  forall v,
    cbv_value v ->
    forall l,
      are_values l ->
      cbv_value (substitute v l).
Proof.
  induction 1; steps; eauto with values; eauto using lookup_value.
Qed.

Hint Resolve cbv_value_subst: values.
