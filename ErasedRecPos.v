Require Import Psatz.
From Equations Require Import Equations.

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Export SystemFR.ErasedRec.
Require Export SystemFR.PolarityLemma.
Require Export SystemFR.ErasedEquivalentPrimitive.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducible_values_rec_pos_induction:
  forall v2,
    is_nat_value v2 ->
    forall v1 ρ T0 Ts t X,
      is_nat_value v1 ->
      twf T0 0 ->
      twf Ts 1 ->
      wf T0 0 ->
      wf Ts 0 ->
      is_erased_type T0 ->
      is_erased_type Ts ->
      pfv T0 term_var = nil ->
      pfv Ts term_var = nil ->
      valid_interpretation ρ ->
      [ ρ ⊨ t : T_rec v2 T0 Ts ]v ->
      [ binary_primitive Lt v1 (succ v2) ≡ ttrue ] ->
       ~(X ∈ pfv T0 type_var) ->
       ~(X ∈ pfv Ts type_var) ->
       ~(X ∈ support ρ) ->
      (forall v,
          [ ρ ⊨ v : topen 0 Ts (T_rec zero T0 Ts) ]v  ->
          [ ρ ⊨ v : T0 ]v) ->
      has_polarities (topen 0 Ts (fvar X type_var)) ((X, Positive) :: nil) ->
      [ ρ ⊨ t : T_rec v1 T0 Ts ]v.
Proof.
  induction 1; destruct 1 as [ | v1' V1Succ ]; repeat step || reducible_values_primitive_Lt_sound;
    eauto 2 using equivalent_true;
    eauto with values;
    eauto with wf;
    try lia.

  - repeat step || simp_red_goal ||  simp_red_top_level_hyp || star_smallstep_value;
       eauto 3 using smallstep_succ_zero with exfalso;
       eauto with values.
    left; repeat step || find_exists || apply_any.
    apply reducible_values_subst_head with X;
      repeat step || list_utils || rewrite nat_value_fv in * by assumption;
      eauto 2 with twf;
      eauto 2 with wf.
    apply (reducible_rename_one _ _ _ _ _ X) in H23; steps; eauto using reducibility_is_candidate.
    eapply positive_grow; eauto 1;
      repeat step || unfold subset_rc || apply reducibility_is_candidate || list_utils;
      eauto with fv wf erased.
    apply IHis_nat_value with X; repeat step || apply equivalent_star || apply tlt_complete2;
      eauto with wf fv;
      eauto using INVSucc;
      eauto with lia;
      t_closer.
    repeat is_nat_value_buildable || steps.
    apply star_one. eapply scbv_step_same; try eapply (SPBetaLt _ _ 0 (S n)) ; eauto with values ; steps.

  - repeat step || simp_red_goal ||  simp_red_top_level_hyp || star_smallstep_value;
      eauto 2 with erased;
      eauto 3 using smallstep_succ_zero with exfalso;
      eauto with values.
    right; repeat step.
    apply (reducible_rename_one _ _ _ _ _ X) in H23; steps; eauto using reducibility_is_candidate.
    exists v1', X; steps.
    eapply positive_grow; eauto 1;
      repeat step || unfold subset_rc || apply reducibility_is_candidate || list_utils;
      eauto with fv wf erased.
    apply IHis_nat_value with X;
      repeat step || list_utils || apply equivalent_star || apply tlt_complete2;
      eauto with erased;
      eauto with wf;
      eauto with fv;
      eauto using INVSucc;
      eauto with lia.
    repeat is_nat_value_buildable || steps.
    apply star_one. eapply scbv_step_same; try eapply (SPBetaLt _ _ n0 (S n)) ; eauto with values ; steps.
    repeat rewrite tree_size_build_nat in *. rewrite PeanoNat.Nat.leb_nle in *. lia.
Qed.

Lemma reducible_values_rec_nat_value:
  forall ρ v t T0 Ts,
    [ ρ ⊨ v : T_rec t T0 Ts ]v ->
    exists n, is_nat_value n /\ t ~>* n.
Proof.
  repeat step || simp_red; eauto with is_nat_value.
Qed.

Ltac reducible_values_rec_nat_value :=
  match goal with
  | H: [ _ ⊨ _ : T_rec ?t _ _ ]v |- _ =>
    poseNew (Mark t "reducible_values_rec_nat_value");
    pose proof (reducible_values_rec_nat_value _ _ _ _ _ H)
  end.

Lemma reducible_values_rec_pos:
  forall t1 t2 ρ T0 Ts t X,
    twf T0 0 ->
    twf Ts 1 ->
    wf T0 0 ->
    wf Ts 0 ->
    is_erased_type T0 ->
    is_erased_type Ts ->
    valid_interpretation ρ ->
    pfv T0 term_var = nil ->
    pfv Ts term_var = nil ->
    [ ρ ⊨ t : T_rec t2 T0 Ts ]v ->
    [ binary_primitive Lt t1 (succ t2) ≡ ttrue ] ->
     ~(X ∈ pfv T0 type_var) ->
     ~(X ∈ pfv Ts type_var) ->
     ~(X ∈ support ρ) ->
    [ ρ ⊨ t1 : T_nat ]  ->
    (forall v,
        [ ρ ⊨ v : topen 0 Ts (T_rec zero T0 Ts) ]v ->
        [ ρ ⊨ v : T0 ]v) ->
    has_polarities (topen 0 Ts (fvar X type_var)) ((X, Positive) :: nil) ->
    [ ρ ⊨ t : T_rec t1 T0 Ts ]v.
Proof.
  unfold reduces_to;
    repeat step || reducible_values_rec_nat_value || simp_red_nat.
  apply reducible_values_rec_backstep with v; t_closer.
  eapply reducible_values_rec_pos_induction; eauto 1; steps;
    eauto using reducible_values_rec_step.
  equivalent_star. eapply_anywhere equivalent_true.
  eapply star_smallstep_binary_primitive_inv in H9 ; steps.
  assert (v = v1). eapply star_smallstep_deterministic; eauto with values.
  assert (succ n = v2). eapply star_smallstep_deterministic; eauto using star_smallstep_succ with values.
  apply star_one ; steps.
Qed.
