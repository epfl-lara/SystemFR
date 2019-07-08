Require Import SystemFR.Trees.
Require Import SystemFR.Syntax.
Require Import SystemFR.StarRelation.
Require Import SystemFR.StarInversions.
Require Import SystemFR.SmallStep.
Require Import SystemFR.Tactics.
Require Import SystemFR.StarLemmas.
Require Import SystemFR.SizeLemmas.
Require Import SystemFR.TermProperties.
Require Import SystemFR.SmallStepIrredLemmas.

Require Import SystemFR.ReducibilityDefinition.
Require Import SystemFR.ReducibilityLemmas.
Require Import SystemFR.ReducibilityCandidate.
Require Import SystemFR.RedTactics.

Require Import Omega.

Lemma reducible_ite_true:
  forall theta v b T1 T2,
    star small_step b ttrue ->
    valid_interpretation theta ->
    reducible_values theta v (T_interpret T1) ->
    reducible_values theta v (T_interpret (ite b T1 T2)).
Proof.
  repeat step || simp_red; eauto using reducible_values_closed.
  eexists; steps; try eassumption; eauto with omega.
  eapply star_smallstep_trans; eauto with bsteplemmas; eauto with smallstep.
Qed.

Lemma reducible_ite_true2:
  forall theta v b T1 T2,
    star small_step b ttrue ->
    valid_interpretation theta ->
    count_interpret T2 = 0 ->
    reducible_values theta v (T_interpret (ite b T1 T2)) ->
    reducible_values theta v (T_interpret T1).
Proof.
  repeat step || simp_red; eauto using reducible_values_closed.
  exists T'; steps; try eassumption; eauto with omega.
  repeat step || t_invert_irred || t_deterministic_star_irred || unfold irred || t_nostep.
Qed.

Lemma reducible_compute_nat:
  forall theta v,
    reducible_values theta v (T_interpret (app (notype_lambda T_nat) uu)) ->
    reducible_values theta v T_nat.
Proof.
  repeat step || simp_red; eauto using reducible_values_closed.
  inversion H1; unfold irred in *; steps.
  - exfalso. apply H with T_nat.
    rewrite <- (WFLemmas.open_none T_nat 0 uu) at 2; steps.
  - inversion H2; repeat step || t_nostep.
    inversion H4; repeat step || simp_red || t_nostep.
Qed.

Lemma reducible_compute_nat2:
  forall theta v,
    reducible_values theta v T_nat ->
    reducible_values theta v (T_interpret (app (notype_lambda T_nat) uu)).
Proof.
  repeat step || simp_red || t_invert_irred; t_closer.
  exists T_nat; repeat step || simp_red || unfold irred || t_nostep.
  apply smallstep_star.
  rewrite <- (WFLemmas.open_none T_nat 0 uu) at 2; steps.
Qed.
