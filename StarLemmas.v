Require Import Termination.Syntax.
Require Import Termination.SmallStep.
Require Import Termination.TermProperties.
Require Import Termination.Tactics.
Require Import Termination.WFLemmas.
Require Import Termination.StarRelation.
Require Import Termination.ListUtils.

Lemma value_irred:
  forall v,
    is_value v ->
    irred v.
Proof.
  unfold irred; repeat step || t_nostep.
Qed.

Lemma values_normalizing:
  forall v,
    is_value v ->
    fv v = nil ->
    wf v 0 ->
    normalizing v.
Proof.
  repeat
    unfold normalizing in * || steps;
    eauto with smallstep.
Qed.

Hint Resolve values_normalizing: norm.

Lemma lambda_normalizing:
  forall t,
    wf t 1 ->
    pfv t term_var = nil ->
    normalizing (notype_lambda t).
Proof.
  repeat step || t_listutils || apply values_normalizing || unfold closed_value, closed_term.
Qed.

Hint Resolve lambda_normalizing: bsteplemmas.

Lemma smallstep_star:
  forall t1 t2,
    small_step t1 t2 ->
    star small_step t1 t2.
Proof.
  steps; eauto with smallstep bwf.
Qed.

Hint Resolve smallstep_star: p_steplemmas.

Lemma star_smallstep_trans:
  forall t1 t2,
    star small_step t1 t2 ->
    forall t3,
      star small_step t2 t3 ->
      star small_step t1 t3.
Proof.
  induction 1; repeat (step || createHypothesis); eauto with smallstep.
Qed.

Lemma star_smallstep_app_l:
  forall t1 t2,
    star small_step t1 t2 ->
    forall t,
      star small_step (app t1 t) (app t2 t).
Proof.
  induction 1; steps; eauto with smallstep step_tactic.
Qed.

Lemma star_smallstep_app_r:
  forall t1 t2,
    star small_step t1 t2 ->
    forall v,
      is_value v ->
      star small_step (app v t1) (app v t2).
Proof.
  induction 1; steps; eauto with smallstep step_tactic bwf.
Qed.

Lemma star_smallstep_pp_l:
  forall t1 t2,
    star small_step t1 t2 ->
    forall t,
      star small_step (pp t1 t) (pp t2 t).
Proof.
  induction 1; steps; eauto with smallstep step_tactic.
Qed.

Lemma star_smallstep_pp_r:
  forall t1 t2,
    star small_step t1 t2 ->
    forall v,
      is_value v ->
      star small_step (pp v t1) (pp v t2).
Proof.
  induction 1; steps; eauto with smallstep.
Qed.

Lemma star_smallstep_err:
  forall t v,
    star small_step t v ->
    t = err ->
    is_value v ->
    False.
Proof.
  inversion 1; repeat step || step_inversion (is_value, small_step).
Qed.

Ltac error_to_value :=
  match goal with
  | H1: star small_step err ?v,
    H2: is_value ?v |- _ =>
    apply False_ind;
    apply (star_smallstep_err _ _ H1 eq_refl H2)
  end.

Hint Extern 50 => error_to_value: bsteplemmas.
Hint Resolve star_smallstep_app_l: bsteplemmas.
Hint Resolve star_smallstep_app_r: bsteplemmas.
Hint Resolve star_smallstep_pp_l: bsteplemmas.
Hint Resolve star_smallstep_pp_r: bsteplemmas.


Lemma star_smallstep_pp:
  forall t1 v t2 t2',
    is_value v ->
    star small_step t1 v ->
    star small_step t2 t2' ->
    star small_step (pp t1 t2) (pp v t2').
Proof.
  steps; eauto using star_smallstep_trans with bsteplemmas.
Qed.

Hint Resolve star_smallstep_pp: bsteplemmas.

Lemma star_smallstep_pi1:
  forall t1 t2,
    star small_step t1 t2 ->
    star small_step (pi1 t1) (pi1 t2).
Proof.
  induction 1; eauto with smallstep.
Qed.

Hint Resolve star_smallstep_pi1: bsteplemmas.

Lemma star_smallstep_pi2:
  forall t1 t2,
    star small_step t1 t2 ->
    star small_step (pi2 t1) (pi2 t2).
Proof.
  induction 1; eauto with smallstep.
Qed.

Hint Resolve star_smallstep_pi2: bsteplemmas.

Lemma star_smallstep_ite_cond:
  forall t1 t2,
    star small_step t1 t2 ->
    forall tt te,
      star small_step (ite t1 tt te) (ite t2 tt te).
Proof.
  induction 1; steps; eauto with smallstep bwf step_tactic.
Qed.

Hint Resolve star_smallstep_ite_cond: bsteplemmas.

Lemma star_smallstep_rec:
  forall t1 t2,
    star small_step t1 t2 ->
    forall tt te,
      star small_step (notype_rec t1 tt te) (notype_rec t2 tt te).
Proof.
  induction 1; steps; eauto with smallstep bwf step_tactic.
Qed.

Hint Resolve star_smallstep_rec: bsteplemmas.

Lemma star_smallstep_match:
  forall t1 t2,
    star small_step t1 t2 ->
    forall tt te,
      star small_step (tmatch t1 tt te) (tmatch t2 tt te).
Proof.
  induction 1; steps; eauto with smallstep bwf step_tactic.
Qed.

Hint Resolve star_smallstep_match: bsteplemmas.

Lemma star_smallstep_succ:
  forall t1 t2,
    star small_step t1 t2 ->
    star small_step (succ t1) (succ t2).
Proof.
  induction 1; steps; eauto with smallstep.
Qed.

Hint Resolve star_smallstep_succ: bsteplemmas.

Lemma star_smallstep_let:
  forall t1 t1' t2,
    star small_step t1 t1' ->
    star small_step (notype_tlet t1 t2) (notype_tlet t1' t2).
Proof.
  induction 1; steps; eauto with smallstep.
Qed.

Hint Resolve star_smallstep_let: bsteplemmas.

Lemma star_smallstep_type_inst:
  forall t1 t1',
    star small_step t1 t1' ->
    star small_step (notype_inst t1) (notype_inst t1').
Proof.
  induction 1; steps; eauto with smallstep.
Qed.

Hint Resolve star_smallstep_type_inst: bsteplemmas.

Lemma star_smallstep_fold:
  forall t1 t1',
    star small_step t1 t1' ->
    star small_step (tfold t1) (tfold t1').
Proof.
  induction 1; steps; eauto with smallstep.
Qed.

Hint Resolve star_smallstep_fold: bsteplemmas.

Lemma star_smallstep_unfold:
  forall t1 t1',
    star small_step t1 t1' ->
    star small_step (tunfold t1) (tunfold t1').
Proof.
  induction 1; steps; eauto with smallstep.
Qed.

Hint Resolve star_smallstep_unfold: bsteplemmas.

Lemma star_smallstep_tleft:
  forall t1 t1',
    star small_step t1 t1' ->
    star small_step (tleft t1) (tleft t1').
Proof.
  induction 1; steps; eauto with smallstep.
Qed.

Hint Resolve star_smallstep_tleft: bsteplemmas.

Lemma star_smallstep_tright:
  forall t1 t1',
    star small_step t1 t1' ->
    star small_step (tright t1) (tright t1').
Proof.
  induction 1; steps; eauto with smallstep.
Qed.

Hint Resolve star_smallstep_tright: bsteplemmas.

Lemma star_smallstep_sum_match:
  forall t1 t1' tl tr,
    star small_step t1 t1' ->
    star small_step (sum_match t1 tl tr) (sum_match t1' tl tr).
Proof.
  induction 1; steps; eauto with smallstep.
Qed.

Hint Resolve star_smallstep_sum_match: bsteplemmas.
