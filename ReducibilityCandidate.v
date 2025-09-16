From Stdlib Require Import PeanoNat.

Require Export SystemFR.ErasedTermLemmas.
Require Export SystemFR.EquivalenceLemmas.

Open Scope list_scope.

Definition reducibility_candidate (P: tree -> Prop): Prop :=
  forall v, P v ->
    is_erased_term v /\
    cbv_value v /\
    wf v 0 /\
    pfv v term_var = nil /\
    (
      forall v1 v2,
        P v1 ->
        [ v1 ≡ v2 ] ->
        cbv_value v2 ->
        P v2
    )
.

(* an interpretation is a map from type variables to reducibility candidates *)
Definition interpretation: Type := list (nat * (tree -> Prop)).

Definition pre_interpretation: Type := list (nat * (tree -> tree -> Prop)).

Fixpoint valid_interpretation (ρ: interpretation): Prop :=
  match ρ with
  | nil => True
  | (x,P) :: ρ' => valid_interpretation ρ' /\ reducibility_candidate P
  end.

Lemma valid_interpretation_cons:
  forall ρ RC X,
    valid_interpretation ρ ->
    reducibility_candidate RC ->
    valid_interpretation ((X, RC) :: ρ).
Proof.
  steps.
Qed.

Lemma in_valid_interpretation_erased: forall ρ v X P,
  valid_interpretation ρ ->
  lookup PeanoNat.Nat.eq_dec ρ X = Some P ->
  P v ->
  is_erased_term v.
Proof.
  induction ρ; repeat step || eauto || apply_any.
Qed.

Lemma in_valid_interpretation_wf: forall ρ v X P,
  valid_interpretation ρ ->
  lookup PeanoNat.Nat.eq_dec ρ X = Some P ->
  P v ->
  wf v 0.
Proof.
  induction ρ; repeat step || eauto || apply_any.
Qed.

Lemma in_valid_interpretation_value: forall ρ v X P,
  valid_interpretation ρ ->
  lookup PeanoNat.Nat.eq_dec ρ X = Some P ->
  P v ->
  cbv_value v.
Proof.
  induction ρ; repeat step || eauto || apply_any.
Qed.

Lemma in_valid_interpretation_fv: forall ρ v X P,
  valid_interpretation ρ ->
  lookup PeanoNat.Nat.eq_dec ρ X = Some P ->
  P v ->
  pfv v term_var = nil.
Proof.
  induction ρ; repeat step || eauto || apply_any.
Qed.

Lemma in_valid_interpretation_tfv: forall ρ v X P,
  valid_interpretation ρ ->
  lookup PeanoNat.Nat.eq_dec ρ X = Some P ->
  P v ->
  pfv v type_var = nil.
Proof.
  intros; eauto using is_erased_term_tfv, in_valid_interpretation_erased.
Qed.

Lemma in_valid_interpretation_pfv: forall ρ v X P tag,
  valid_interpretation ρ ->
  lookup PeanoNat.Nat.eq_dec ρ X = Some P ->
  P v ->
  pfv v tag = nil.
Proof.
  destruct tag; eauto using in_valid_interpretation_fv, in_valid_interpretation_tfv.
Qed.

Lemma in_valid_interpretation_twf: forall ρ v X P,
  valid_interpretation ρ ->
  lookup PeanoNat.Nat.eq_dec ρ X = Some P ->
  P v ->
  twf v 0.
Proof.
  eauto using is_erased_term_twf, in_valid_interpretation_erased.
Qed.

Lemma in_valid_interpretation_equiv: forall ρ v1 v2 X P,
  valid_interpretation ρ ->
  lookup PeanoNat.Nat.eq_dec ρ X = Some P ->
  P v1 ->
  [ v1 ≡ v2 ] ->
  cbv_value v2 ->
  P v2.
Proof.
  induction ρ; repeat step || unfold reducibility_candidate in * || instantiate_any;
    try solve [ eapply_any; eauto ].
Qed.

Lemma in_valid_interpretation_equiv2: forall ρ v1 v2 X P,
  valid_interpretation ρ ->
  lookup PeanoNat.Nat.eq_dec ρ X = Some P ->
  P v1 ->
  [ v2 ≡ v1 ] ->
  cbv_value v2 ->
  P v2.
Proof.
  intros.
  eapply in_valid_interpretation_equiv; eauto using equivalent_sym.
Qed.

Fixpoint valid_pre_interpretation (P: tree -> Prop) (ρ: list (nat * (tree -> tree -> Prop))) : Prop :=
  match ρ with
  | nil => True
  | (_, RC) :: ρ' => valid_pre_interpretation P ρ' /\ forall a, P a -> reducibility_candidate (RC a)
  end.

Lemma valid_interpretation_equiv:
  forall P1 P2 pre_ρ,
    valid_pre_interpretation P1 pre_ρ ->
    (forall x, P1 x <-> P2 x) ->
    valid_pre_interpretation P2 pre_ρ.
Proof.
  induction pre_ρ; steps; eauto with eapply_any.
Qed.

Ltac t_valid_interpretation_equiv :=
  match goal with
  | H1: valid_pre_interpretation ?P1 ?pre_ρ |- valid_pre_interpretation _ ?pre_ρ => apply valid_interpretation_equiv with P1
  end.

Definition push_one (a: tree) (l: list (nat * (tree -> tree -> Prop))): interpretation :=
  map_values (fun rc => rc a) l.
Definition push_all (P: tree -> Prop) (l: list (nat * (tree -> tree -> Prop))): interpretation :=
  map_values (fun (rc: tree -> tree -> Prop) (v: tree) => (forall a, P a -> rc a v)) l.

Lemma valid_interpretation_one:
  forall a (P: tree -> Prop) ρ,
    P a ->
    valid_pre_interpretation P ρ ->
    valid_interpretation (push_one a ρ).
Proof.
  induction ρ; steps.
Qed.

Lemma valid_interpretation_append:
  forall ρ1 ρ2,
    valid_interpretation ρ1 ->
    valid_interpretation ρ2 ->
    valid_interpretation (ρ1 ++ ρ2).
Proof.
  induction ρ1; steps.
Qed.

#[export]
Hint Resolve valid_interpretation_cons: b_valid_interp.
#[export]
Hint Resolve valid_interpretation_one: b_valid_interp.

#[export]
Hint Resolve valid_interpretation_append: b_valid_interp.
#[export]
Hint Extern 1 => eapply valid_interpretation_one; eauto: b_valid_interp.
