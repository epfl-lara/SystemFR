From Equations Require Import Equations.

Require Export SystemFR.RedTactics.

Opaque reducible_values.

Lemma reducible_values_tsize:
  forall ρ n,
    [ ρ ⊨ build_nat n : T_nat ]v.
Proof.
  repeat step || simp_red;
    eauto using is_nat_value_build_nat.
Qed.

Lemma reducible_tsize:
  forall ρ t T,
    valid_interpretation ρ ->
    [ ρ ⊨ t : T ] ->
    [ ρ ⊨ tsize t : T_nat ].
Proof.
  unfold reduces_to; repeat step.
  eexists (build_nat (tsize_semantics v)); steps; eauto using reducible_values_tsize.
  eapply star_trans; eauto with cbvlemmas.
  apply star_one.
  constructor;
    eauto using red_is_val;
    eauto using fv_nil_top_level_var with fv.
Qed.

Lemma open_reducible_tsize:
  forall Θ Γ t T,
    [ Θ; Γ ⊨ t : T ] ->
    [ Θ; Γ ⊨ tsize t : T_nat ].
Proof.
  unfold open_reducible; steps;
    eauto using reducible_tsize.
Qed.
