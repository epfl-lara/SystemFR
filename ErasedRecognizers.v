From Equations Require Import Equations.

Require Export SystemFR.RedTactics.

Opaque reducible_values.

Lemma reducible_values_is_pair:
  forall ρ v,
    [ ρ ⊨ is_pair v : T_bool ]v.
Proof.
  destruct v; repeat step || simp_red.
Qed.

Lemma reducible_values_is_succ:
  forall ρ v,
    [ ρ ⊨ is_succ v : T_bool ]v.
Proof.
  destruct v; repeat step || simp_red.
Qed.

Lemma reducible_values_is_lambda:
  forall ρ v,
    [ ρ ⊨ is_lambda v : T_bool ]v.
Proof.
  destruct v; repeat step || simp_red.
Qed.

Lemma reducible_is_pair:
  forall ρ t,
    valid_interpretation ρ ->
    [ ρ ⊨ t : T_top ] ->
    [ ρ ⊨ boolean_recognizer 0 t : T_bool ].
Proof.
  unfold reduces_to; repeat step.
  exists (is_pair v); steps; eauto using reducible_values_is_pair.
  eapply star_trans; eauto with cbvlemmas.
  apply star_one.
  constructor;
    eauto using red_is_val;
    eauto using fv_nil_top_level_var with fv.
Qed.

Lemma reducible_is_succ:
  forall ρ t,
    valid_interpretation ρ ->
    [ ρ ⊨ t : T_top ] ->
    [ ρ ⊨ boolean_recognizer 1 t : T_bool ].
Proof.
  unfold reduces_to; repeat step.
  exists (is_succ v); steps; eauto using reducible_values_is_succ.
  eapply star_trans; eauto with cbvlemmas.
  apply star_one.
  constructor;
    eauto using red_is_val;
    eauto using fv_nil_top_level_var with fv.
Qed.

Lemma reducible_is_lambda:
  forall ρ t,
    valid_interpretation ρ ->
    [ ρ ⊨ t : T_top ] ->
    [ ρ ⊨ boolean_recognizer 2 t : T_bool ].
Proof.
  unfold reduces_to; repeat step.
  exists (is_lambda v); steps; eauto using reducible_values_is_lambda.
  eapply star_trans; eauto with cbvlemmas.
  apply star_one.
  constructor;
    eauto using red_is_val;
    eauto using fv_nil_top_level_var with fv.
Qed.

Lemma open_reducible_is_pair:
  forall Θ Γ t,
    [ Θ; Γ ⊨ t : T_top ] ->
    [ Θ; Γ ⊨ boolean_recognizer 0 t : T_bool ].
Proof.
  unfold open_reducible; steps; eauto using reducible_is_pair.
Qed.

Lemma open_reducible_is_succ:
  forall Θ Γ t,
    [ Θ; Γ ⊨ t : T_top ] ->
    [ Θ; Γ ⊨ boolean_recognizer 1 t : T_bool ].
Proof.
  unfold open_reducible; steps; eauto using reducible_is_succ.
Qed.

Lemma open_reducible_is_lambda:
  forall Θ Γ t,
    [ Θ; Γ ⊨ t : T_top ] ->
    [ Θ; Γ ⊨ boolean_recognizer 2 t : T_bool ].
Proof.
  unfold open_reducible; steps; eauto using reducible_is_lambda.
Qed.
