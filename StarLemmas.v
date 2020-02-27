Require Export SystemFR.SmallStep.
Require Export SystemFR.RelationClosures.
Require Export SystemFR.ListUtils.

Definition scbv_normalizing t: Prop :=
  exists v, cbv_value v /\ star scbv_step t v.

Lemma value_normalizing:
  forall v,
    cbv_value v ->
    scbv_normalizing v.
Proof.
  unfold scbv_normalizing; eauto with star.
Qed.

Definition irred t :=
  forall t', ~scbv_step t t'.

Lemma value_irred:
  forall v,
    cbv_value v ->
    irred v.
Proof.
  unfold irred; repeat step || no_step.
Qed.

Lemma values_normalizing:
  forall v,
    cbv_value v ->
    fv v = nil ->
    wf v 0 ->
    scbv_normalizing v.
Proof.
  repeat
    unfold scbv_normalizing in * || steps;
    eauto with smallstep star.
Qed.

Hint Resolve values_normalizing: norm.

Lemma lambda_normalizing:
  forall t,
    wf t 1 ->
    pfv t term_var = nil ->
    pfv t type_var = nil ->
    scbv_normalizing (notype_lambda t).
Proof.
  repeat step || list_utils || apply values_normalizing || unfold closed_value, closed_term;
    eauto with values.
Qed.

Hint Resolve lambda_normalizing: cbvlemmas.

Lemma smallstep_star:
  forall t1 t2,
    scbv_step t1 t2 ->
    star scbv_step t1 t2.
Proof.
  steps; eauto with smallstep star.
Qed.

Hint Resolve smallstep_star: cbvlemmas.

Lemma star_smallstep_app_l:
  forall t1 t2,
    star scbv_step t1 t2 ->
    forall t,
      star scbv_step (app t1 t) (app t2 t).
Proof.
  induction 1; steps; eauto with smallstep star.
Qed.

Lemma star_smallstep_app_r:
  forall t1 t2,
    star scbv_step t1 t2 ->
    forall v,
      cbv_value v ->
      star scbv_step (app v t1) (app v t2).
Proof.
  induction 1; steps; eauto with smallstep star.
Qed.

Lemma star_smallstep_pp_l:
  forall t1 t2,
    star scbv_step t1 t2 ->
    forall t,
      star scbv_step (pp t1 t) (pp t2 t).
Proof.
  induction 1; steps; eauto with smallstep star.
Qed.

Lemma star_smallstep_pp_r:
  forall t1 t2,
    star scbv_step t1 t2 ->
    forall v,
      cbv_value v ->
      star scbv_step (pp v t1) (pp v t2).
Proof.
  induction 1; steps; eauto with smallstep star.
Qed.

Lemma star_smallstep_err:
  forall t v,
    star scbv_step t v ->
    t = notype_err ->
    cbv_value v ->
    False.
Proof.
  inversion 1; repeat step || step_inversion (cbv_value, scbv_step).
Qed.

Ltac error_to_value :=
  match goal with
  | H1: star scbv_step err ?v,
    H2: cbv_value ?v |- _ =>
    apply False_ind;
    apply (star_smallstep_err _ _ H1 eq_refl H2)
  end.

Hint Extern 50 => error_to_value: cbvlemmas.
Hint Resolve star_smallstep_app_l: cbvlemmas.
Hint Resolve star_smallstep_app_r: cbvlemmas.
Hint Resolve star_smallstep_pp_l: cbvlemmas.
Hint Resolve star_smallstep_pp_r: cbvlemmas.


Lemma star_smallstep_pp:
  forall t1 v t2 t2',
    cbv_value v ->
    star scbv_step t1 v ->
    star scbv_step t2 t2' ->
    star scbv_step (pp t1 t2) (pp v t2').
Proof.
  steps; eauto using star_trans with cbvlemmas.
Qed.

Hint Resolve star_smallstep_pp: cbvlemmas.

Lemma star_smallstep_pi1:
  forall t1 t2,
    star scbv_step t1 t2 ->
    star scbv_step (pi1 t1) (pi1 t2).
Proof.
  induction 1; eauto with smallstep star.
Qed.

Hint Resolve star_smallstep_pi1: cbvlemmas.

Lemma star_smallstep_pi2:
  forall t1 t2,
    star scbv_step t1 t2 ->
    star scbv_step (pi2 t1) (pi2 t2).
Proof.
  induction 1; eauto with smallstep star.
Qed.

Hint Resolve star_smallstep_pi2: cbvlemmas.

Lemma star_smallstep_ite_cond:
  forall t1 t2,
    star scbv_step t1 t2 ->
    forall tt te,
      star scbv_step (ite t1 tt te) (ite t2 tt te).
Proof.
  induction 1; steps; eauto with smallstep star.
Qed.

Hint Resolve star_smallstep_ite_cond: cbvlemmas.

Lemma star_smallstep_match:
  forall t1 t2,
    star scbv_step t1 t2 ->
    forall tt te,
      star scbv_step (tmatch t1 tt te) (tmatch t2 tt te).
Proof.
  induction 1; steps; eauto with smallstep star.
Qed.

Hint Resolve star_smallstep_match: cbvlemmas.

Lemma star_smallstep_succ:
  forall t1 t2,
    star scbv_step t1 t2 ->
    star scbv_step (succ t1) (succ t2).
Proof.
  induction 1; steps; eauto with smallstep star.
Qed.

Hint Resolve star_smallstep_succ: cbvlemmas.

Lemma star_smallstep_tleft:
  forall t1 t1',
    star scbv_step t1 t1' ->
    star scbv_step (tleft t1) (tleft t1').
Proof.
  induction 1; steps; eauto with smallstep star.
Qed.

Hint Resolve star_smallstep_tleft: cbvlemmas.

Lemma star_smallstep_tright:
  forall t1 t1',
    star scbv_step t1 t1' ->
    star scbv_step (tright t1) (tright t1').
Proof.
  induction 1; steps; eauto with smallstep star.
Qed.

Hint Resolve star_smallstep_tright: cbvlemmas.

Lemma star_smallstep_sum_match:
  forall t1 t1' tl tr,
    star scbv_step t1 t1' ->
    star scbv_step (sum_match t1 tl tr) (sum_match t1' tl tr).
Proof.
  induction 1; steps; eauto with smallstep star.
Qed.

Hint Resolve star_smallstep_sum_match: cbvlemmas.

Lemma star_smallstep_tsize:
  forall t1 t1',
    star scbv_step t1 t1' ->
    star scbv_step (tsize t1) (tsize t1').
Proof.
  induction 1; steps; eauto with smallstep star.
Qed.

Hint Resolve star_smallstep_tsize: cbvlemmas.

Lemma star_smallstep_recognizer:
  forall t1 t1' r,
    star scbv_step t1 t1' ->
    star scbv_step (boolean_recognizer r t1) (boolean_recognizer r t1').
Proof.
  induction 1; steps; eauto with smallstep star.
Qed.

Hint Resolve star_smallstep_recognizer: cbvlemmas.
