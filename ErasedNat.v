Require Import Equations.Equations.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Require Export SystemFR.ErasedArrow.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducible_value_zero:
  forall ρ, [ ρ ⊨ zero : T_nat ]v.
Proof.
  repeat step || simp_red.
Qed.

Lemma reducible_zero:
  forall ρ, [ ρ ⊨ zero : T_nat ].
Proof.
  repeat step || simp_red || unfold reduces_to || eexists || constructor.
Qed.

Lemma open_reducible_zero:
  forall Θ Γ,
    [ Θ; Γ ⊨ zero : T_nat ].
Proof.
  unfold open_reducible; steps;
    auto using reducible_zero.
Qed.

Lemma reducible_values_succ:
  forall ρ v,
    [ ρ ⊨ v : T_nat ]v ->
    [ ρ ⊨ succ v : T_nat ]v.
Proof.
  repeat step || simp_red; eauto with is_nat_value.
Qed.

Lemma reducible_succ:
  forall ρ t,
    valid_interpretation ρ ->
    [ ρ ⊨ t : T_nat ]  ->
    [ ρ ⊨ succ t : T_nat ].
Proof.
  unfold reduces_to; steps.
  exists (succ v); repeat step || simp_red; eauto with cbvlemmas;
    eauto with is_nat_value.
Qed.

Lemma reducible_nat_value:
  forall ρ v,
    is_nat_value v ->
    valid_interpretation ρ ->
    [ ρ ⊨ v : T_nat ]v.
Proof.
  induction 1; repeat step;
    eauto using reducible_value_zero;
    eauto using reducible_values_succ.
Qed.

Lemma reducible_nat:
  forall ρ v,
    is_nat_value v ->
    valid_interpretation ρ ->
    [ ρ ⊨ v : T_nat ].
Proof.
  induction 1; repeat step;
    eauto using reducible_zero;
    eauto using reducible_succ.
Qed.

Lemma open_reducible_succ:
  forall Θ Γ t,
    [ Θ; Γ ⊨ t : T_nat ] ->
    [ Θ; Γ ⊨ succ t : T_nat ].
Proof.
  unfold open_reducible in *; steps;
    eauto using reducible_succ.
Qed.

Lemma reducible_match:
  forall ρ tn t0 ts T,
    fv ts = nil ->
    fv t0 = nil ->
    wf t0 0 ->
    wf ts 1 ->
    is_erased_term t0 ->
    is_erased_term ts ->
    valid_interpretation ρ ->
    [ ρ ⊨ tn : T_nat ]  ->
    ([ tn ≡ zero ] -> [ ρ ⊨ t0 : T ] ) ->
     (forall n,
        [ tn ≡ succ n ] ->
        [ ρ ⊨ n : T_nat ]v ->
        [ ρ ⊨ open 0 ts n : T ]) ->
    [ ρ ⊨ tmatch tn t0 ts : T ].
Proof.
  steps.
  unfold reduces_to in H6; steps.
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
      | H: forall n, _ -> _ -> [ _ ⊨ _ : _ ]  |-  _ => apply H
      end;
      eauto 4 with smallstep values;
      auto 2 with fv;
      eauto 2 with wf;
      eauto with erased;
      try solve [ eapply equivalent_star; steps; t_closer ].
Qed.

Lemma open_reducible_match:
  forall Θ tn t0 ts Γ T n p,
    wf ts 1 ->
    wf t0 0 ->
    subset (fv ts) (support Γ) ->
    subset (fv t0) (support Γ) ->
    ~(p ∈ fv tn) ->
    ~(p ∈ fv T) ->
    ~(p ∈ fv_context Γ) ->
    ~(n ∈ fv tn) ->
    ~(n ∈ fv ts) ->
    ~(n ∈ fv T) ->
    ~(n ∈ fv_context Γ) ->
    ~(p = n) ->
    is_erased_term t0 ->
    is_erased_term ts ->
    [ Θ; Γ ⊨ tn : T_nat ] ->
    [ Θ; (p, T_equiv tn zero) :: Γ ⊨ t0 : T ] ->
    [ Θ;
        (p, T_equiv tn (succ (fvar n term_var))) ::
        (n, T_nat) ::
        Γ ⊨
          open 0 ts (fvar n term_var) : T ] ->
    [ Θ; Γ ⊨ tmatch tn t0 ts : T ].
Proof.
  unfold open_reducible; repeat step || t_instantiate_sat3.

  apply reducible_match; repeat step || t_termlist;
    eauto with wf;
    eauto using subset_same with fv;
    eauto with erased.

  - (* zero *)
    unshelve epose proof (H14 ρ ((p, uu) :: lterms) _ _ _);
      repeat step || apply SatCons || simp_red || t_substitutions;
      t_closer.

  - (* successor *)
    unshelve epose proof (H15 ρ ((p, uu) :: (n,n0) :: lterms) _ _ _);
      repeat step || apply SatCons || simp_red || t_substitutions;
      t_closer;
      eauto with twf.
Qed.
