Require Import SystemFR.WFLemmas.
Require Import SystemFR.Tactics.
Require Import SystemFR.Syntax.
Require Import SystemFR.SmallStep.
Require Import SystemFR.TermProperties.
Require Import SystemFR.ListUtils.
Require Import SystemFR.SizeLemmas.
Require Import SystemFR.StarRelation.
Require Import SystemFR.PrimitiveRecognizers.

Lemma wf_nat_value:
  forall v, is_nat_value v -> wf v 0.
Proof.
  induction 1; steps.
Qed.

Hint Immediate wf_nat_value: bwf.

Lemma twf_nat_value:
  forall v, is_nat_value v -> twf v 0.
Proof.
  induction 1; steps.
Qed.

Hint Immediate twf_nat_value: btwf.

Lemma wf_is_pair:
  forall v, wf (is_pair v) 0.
Proof.
  destruct v; steps.
Qed.

Hint Immediate wf_is_pair: bwf.

Lemma wf_is_succ:
  forall v, wf (is_succ v) 0.
Proof.
  destruct v; steps.
Qed.

Hint Immediate wf_is_succ: bwf.

Lemma wf_is_lambda:
  forall v, wf (is_lambda v) 0.
Proof.
  destruct v; steps.
Qed.

Hint Immediate wf_is_lambda: bwf.

Lemma wf_smallstep:
  forall t1 t2,
    small_step t1 t2 ->
    wf t1 0 ->
    wf t2 0.
Proof.
  induction 1; steps; eauto using is_nat_value_build_nat with step_tactic bwf.
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
