From Equations Require Import Equations.

From Stdlib Require Import PeanoNat.
From Stdlib Require Import List.

Require Export SystemFR.ReducibilityOpenEquivalent.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducible_values_pp:
  forall ρ v1 v2 T1 T2,
    valid_interpretation ρ ->
    [ ρ ⊨ v1 : T1 ]v ->
    [ ρ ⊨ v2 : open 0 T2 v1 ]v ->
    is_erased_type T2 ->
    [ ρ ⊨ pp v1 v2 : T_prod T1 T2 ]v.
Proof.
  repeat step || simp reducible_values || t_closer ||
         rewrite reducibility_rewrite || unshelve exists v1, v2;
    eauto with erased;
    eauto with fv;
    eauto with wf;
    eauto with values.
Qed.

Lemma reducible_pp:
  forall ρ U V t1 t2,
    valid_interpretation ρ ->
    is_erased_type V ->
    wf V 1 ->
    pfv V term_var = nil ->
    [ ρ ⊨ t1 : U ] ->
    [ ρ ⊨ t2 : open 0 V t1 ] ->
    [ ρ ⊨ pp t1 t2 : T_prod U V ].
Proof.
  unfold reduces_to; repeat step || list_utils; try t_closer.

  exists (pp v0 v); repeat step || simp_red;
    try t_closer;
    eauto using red_is_val with cbvlemmas.

  eexists; eexists; steps; eauto with erased wf fv.
  eapply reducibility_values_ltr; eauto; steps;
    eauto with wf;
    try t_closer.
Qed.

Lemma open_reducible_pp:
  forall Θ Γ U V t1 t2,
    is_erased_type V ->
    wf V 1 ->
    subset (fv V) (support Γ) ->
    [ Θ; Γ ⊨ t1 : U ] ->
    [ Θ; Γ ⊨ t2 : open 0 V t1 ] ->
    [ Θ; Γ ⊨ pp t1 t2 : T_prod U V ].
Proof.
  unfold open_reducible in *; steps; eauto using reducible_pp.
  apply reducible_pp; repeat step;
    eauto with erased;
    eauto with fv;
    try solve [ unshelve eauto with wf; auto ].
  rewrite <- substitute_open; steps; eauto with wf.
Qed.

Lemma reducible_values_pi1:
  forall ρ U V t,
    valid_interpretation ρ ->
    [ ρ ⊨ t : T_prod U V ]v ->
    [ ρ ⊨ pi1 t : U ].
Proof.
  repeat step || t_values_info2 || simp_red.
  eapply backstep_reducible; repeat step || list_utils;
    eauto with smallstep;
    eauto with fv wf;
    eauto using reducible_value_expr;
    eauto with erased.
Qed.

Lemma reducible_pi1:
  forall ρ U V t,
    valid_interpretation ρ ->
    [ ρ ⊨ t : T_prod U V ] ->
    [ ρ ⊨ pi1 t : U ].
Proof.
  intros ρ U V t HV H.
  unfold reduces_to in H; steps.
  eapply star_backstep_reducible; steps;
    eauto with cbvlemmas;
    eauto using reducible_values_pi1;
    try t_closer.
Qed.

Lemma open_reducible_pi1:
  forall Θ Γ U V t,
    [ Θ; Γ ⊨ t : T_prod U V ] ->
    [ Θ; Γ ⊨ pi1 t : U ].
Proof.
  unfold open_reducible in *; steps; eauto using reducible_pi1.
Qed.

Lemma reducible_values_pi2:
  forall ρ U V t,
    valid_interpretation ρ ->
    wf V 1 ->
    pfv V term_var = nil ->
    [ ρ ⊨ t : T_prod U V ]v ->
    [ ρ ⊨ pi2 t : open 0 V (pi1 t) ].
Proof.
  repeat step || t_values_info2 || simp_red.
  eapply backstep_reducible; repeat step || list_utils || simp_red;
    eauto with smallstep;
    eauto with fv wf;
    eauto using reducible_value_expr;
    eauto with erased.

  apply reducible_value_expr; auto.
  eapply reducibility_values_rtl; repeat step || list_utils;
    eauto with wf;
    eauto with erased;
    eauto with fv;
    eauto using star_one with smallstep.
Qed.

Lemma reducible_pi2:
  forall ρ U V t,
    valid_interpretation ρ ->
    is_erased_type V ->
    wf V 1 ->
    pfv V term_var = nil ->
    [ ρ ⊨ t : T_prod U V ] ->
    [ ρ ⊨ pi2 t : open 0 V (pi1 t) ].
Proof.
  repeat step || top_level_unfold reduces_to.
  eapply star_backstep_reducible; eauto with cbvlemmas; t_closer.
  eapply reducibility_rtl; eauto with cbvlemmas; t_closer;
    eauto using reducible_values_pi2.
Qed.

Lemma reducible_pi2_nodep:
  forall ρ U V t,
    valid_interpretation ρ ->
    is_erased_type V ->
    wf V 0 ->
    pfv V term_var = nil ->
    [ ρ ⊨ t : T_prod U V ] ->
    [ ρ ⊨ pi2 t : V ].
Proof.
  intros.
  unshelve epose proof (reducible_pi2 ρ U V t _ _ _ _ _); repeat step || open_none;
    eauto with wf.
Qed.

Lemma open_reducible_pi2:
  forall Θ Γ U V t,
    is_erased_type V ->
    wf V 1 ->
    subset (fv V) (support Γ) ->
    [ Θ; Γ ⊨ t : T_prod U V ] ->
    [ Θ; Γ ⊨ pi2 t : open 0 V (pi1 t) ].
Proof.
  unfold open_reducible in *; repeat step || t_substitutions.
  eapply reducible_pi2;
    eauto with erased;
    eauto with fv;
    try solve [ unshelve eauto with wf; auto ].
Qed.

Lemma reducible_unit:
  forall ρ, [ ρ ⊨ uu : T_unit ].
Proof.
  repeat step || simp_red || unfold reduces_to || eexists;
    eauto with smallstep step_tactic.
Qed.

Lemma open_reducible_unit:
  forall Θ Γ,
    [ Θ; Γ ⊨ uu : T_unit ].
Proof.
  unfold open_reducible in *; repeat step;
    auto using reducible_unit.
Qed.
