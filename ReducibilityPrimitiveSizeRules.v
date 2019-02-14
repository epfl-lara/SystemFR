Require Import Equations.Equations.

Require Import Termination.Tactics.
Require Import Termination.Trees.
Require Import Termination.Syntax.
Require Import Termination.TermList.
Require Import Termination.AssocList.
Require Import Termination.StarRelation.
Require Import Termination.SmallStep.
Require Import Termination.PrimitiveSize.
Require Import Termination.StarLemmas.

Require Import Termination.ReducibilityDefinition.
Require Import Termination.ReducibilityLemmas.
Require Import Termination.ReducibilityCandidate.
Require Import Termination.RedTactics.

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
  eexists (build_nat (tsize_semantics t')); steps; eauto using reducible_values_tsize;
    eauto 6 using star_smallstep_trans, red_is_val with bsteplemmas smallstep.
Qed.

Lemma open_reducible_tsize:
  forall tvars gamma t T,
    open_reducible tvars gamma t T ->
    open_reducible tvars gamma (tsize t) T_nat.
Proof.
  unfold open_reducible; steps;
    eauto using reducible_tsize.
Qed.
