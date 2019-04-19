Require Import Equations.Equations.

Require Import SystemFR.Tactics.
Require Import SystemFR.Trees.
Require Import SystemFR.Syntax.
Require Import SystemFR.TermList.
Require Import SystemFR.AssocList.
Require Import SystemFR.StarRelation.
Require Import SystemFR.SmallStep.
Require Import SystemFR.PrimitiveSize.
Require Import SystemFR.StarLemmas.

Require Import SystemFR.ReducibilityDefinition.
Require Import SystemFR.ReducibilityLemmas.
Require Import SystemFR.ReducibilityCandidate.
Require Import SystemFR.RedTactics.

Opaque reducible_values.

Lemma reducible_values_tsize:
  forall theta n,
    reducible_values theta (build_nat n) T_nat.
Proof.
  repeat step || simp_red;
    eauto using is_nat_value_build_nat.
Qed.

Lemma reducible_tsize:
  forall theta t T,
    valid_interpretation theta ->
    reducible theta t T ->
    reducible theta (tsize t) T_nat.
Proof.
  unfold reducible, reduces_to; repeat step.
  eexists (build_nat (tsize_semantics t')); steps; eauto using reducible_values_tsize.
  eauto 7 using star_smallstep_trans, red_is_val with bsteplemmas smallstep bfv.
Qed.

Lemma open_reducible_tsize:
  forall tvars gamma t T,
    open_reducible tvars gamma t T ->
    open_reducible tvars gamma (tsize t) T_nat.
Proof.
  unfold open_reducible; steps;
    eauto using reducible_tsize.
Qed.
