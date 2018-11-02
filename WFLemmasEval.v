Require Import Termination.WFLemmas.
Require Import Termination.Tactics.
Require Import Termination.Syntax.
Require Import Termination.SmallStep.
Require Import Termination.TermProperties.
Require Import Termination.ListUtils.
Require Import Termination.SizeLemmas.
Require Import Termination.StarRelation.

Lemma wf_smallstep:
  forall t1 t2,
    small_step t1 t2 ->
    wf t1 0 ->
    wf t2 0.
Proof.
  induction 1; steps; eauto with step_tactic bwf.
Qed.

Hint Resolve wf_smallstep: bwf.

Lemma wf_star_smallstep:
  forall t1 t2,
    star small_step t1 t2 ->
    wf t1 0 ->
    wf t2 0.
Proof.
  induction 1; steps; eauto using wf_smallstep.
Qed.

Hint Resolve wf_star_smallstep: bwf.

Lemma wf_nat_value:
  forall v, is_nat_value v -> wf v 0.
Proof.
  induction v; steps.
Qed.

Hint Resolve wf_nat_value: bwf.
