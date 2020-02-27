Require Import Equations.Equations.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Require Export SystemFR.ErasedArrow.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducible_value_zero:
  forall theta, reducible_values theta zero T_nat.
Proof.
  repeat step || simp_red.
Qed.

Lemma reducible_zero:
  forall theta, reducible theta zero T_nat.
Proof.
  repeat step || simp_red || unfold reducible, reduces_to || eexists || constructor.
Qed.

Lemma open_reducible_zero:
  forall tvars gamma,
    [ tvars; gamma ⊨ zero : T_nat ].
Proof.
  unfold open_reducible in *; repeat step;
    auto using reducible_zero.
Qed.

Lemma reducible_values_succ:
  forall theta v,
    reducible_values theta v T_nat ->
    reducible_values theta (succ v) T_nat.
Proof.
  repeat step || simp_red; eauto with is_nat_value.
Qed.

Lemma reducible_succ:
  forall theta t,
    valid_interpretation theta ->
    reducible theta t T_nat ->
    reducible theta (succ t) T_nat.
Proof.
  unfold reducible, reduces_to; steps.
  exists (succ v); repeat step || simp_red; eauto with cbvlemmas;
    eauto with is_nat_value.
Qed.

Lemma reducible_nat_value:
  forall theta v,
    is_nat_value v ->
    valid_interpretation theta ->
    reducible_values theta v T_nat.
Proof.
  induction 1; repeat step;
    eauto using reducible_value_zero;
    eauto using reducible_values_succ.
Qed.

Lemma reducible_nat:
  forall theta v,
    is_nat_value v ->
    valid_interpretation theta ->
    reducible theta v T_nat.
Proof.
  induction 1; repeat step;
    eauto using reducible_zero;
    eauto using reducible_succ.
Qed.

Lemma open_reducible_succ:
  forall tvars gamma t,
    [ tvars; gamma ⊨ t : T_nat ] ->
    [ tvars; gamma ⊨ succ t : T_nat ].
Proof.
  unfold open_reducible in *; steps;
    eauto using reducible_succ.
Qed.

Lemma reducible_match:
  forall theta tn t0 ts T,
    fv ts = nil ->
    fv t0 = nil ->
    wf t0 0 ->
    wf ts 1 ->
    is_erased_term t0 ->
    is_erased_term ts ->
    valid_interpretation theta ->
    reducible theta tn T_nat ->
    (equivalent_terms tn zero -> reducible theta t0 T) ->
     (forall n,
        equivalent_terms tn (succ n) ->
        reducible_values theta n T_nat ->
        reducible
          theta
          (open 0 ts n)
          T) ->
    reducible theta (tmatch tn t0 ts) T.
Proof.
  steps.
  unfold reducible, reduces_to in H6; steps.
  eapply star_backstep_reducible with (tmatch v t0 ts);
    repeat step || list_utils || simp_red; t_closer;
      eauto with cbvlemmas.

  t_invert_nat_value; steps.

  - (* zero *)
    eapply backstep_reducible; eauto with smallstep;
      repeat step || list_utils || apply_any; eauto with fv;
      try solve [ eapply equivalent_star; steps; t_closer ].

  - (* succ v *)
    apply backstep_reducible with (open 0 ts v0);
      repeat step || list_utils || apply reducible_nat_value ||
      match goal with
      | H: forall n, _ -> _ -> reducible _ _ _ |-  _ => apply H
      end;
      eauto 4 with smallstep values;
      auto 2 with fv;
      eauto 2 with wf;
      eauto with erased;
      try solve [ eapply equivalent_star; steps; t_closer ].
Qed.

Lemma open_reducible_match:
  forall tvars tn t0 ts gamma T n p,
    wf ts 1 ->
    wf t0 0 ->
    subset (fv ts) (support gamma) ->
    subset (fv t0) (support gamma) ->
    ~(p ∈ fv tn) ->
    ~(p ∈ fv T) ->
    ~(p ∈ fv_context gamma) ->
    ~(n ∈ fv tn) ->
    ~(n ∈ fv ts) ->
    ~(n ∈ fv T) ->
    ~(n ∈ fv_context gamma) ->
    ~(p = n) ->
    is_erased_term t0 ->
    is_erased_term ts ->
    [ tvars; gamma ⊨ tn : T_nat ] ->
    [ tvars; (p, T_equiv tn zero) :: gamma ⊨ t0 : T ] ->
    [ tvars;
        (p, T_equiv tn (succ (fvar n term_var))) ::
        (n, T_nat) ::
        gamma ⊨
          open 0 ts (fvar n term_var) : T ] ->
    [ tvars; gamma ⊨ tmatch tn t0 ts : T ].
Proof.
  unfold open_reducible in *; repeat step || t_instantiate_sat3.

  apply reducible_match; repeat step || t_termlist;
    eauto with wf;
    eauto using subset_same with fv;
    eauto with erased.

  - (* zero *)
    unshelve epose proof (H14 theta ((p, uu) :: lterms) _ _ _);
      repeat step || apply SatCons || simp_red || t_substitutions;
      t_closer.

  - (* successor *)
    unshelve epose proof (H15 theta ((p, uu) :: (n,n0) :: lterms) _ _ _);
      repeat step || apply SatCons || simp_red || t_substitutions;
      t_closer;
      eauto with twf.
Qed.
