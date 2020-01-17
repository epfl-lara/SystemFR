Require Export SystemFR.WFLemmas.
Require Export SystemFR.SmallStep.
Require Export SystemFR.SizeLemmas.
Require Export SystemFR.PrimitiveRecognizers.
Require Export SystemFR.RelationClosures.

Lemma wf_nat_value:
  forall v, is_nat_value v -> wf v 0.
Proof.
  induction 1; steps.
Qed.

Hint Immediate wf_nat_value: wf.

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

Hint Immediate wf_is_pair: wf.

Lemma wf_is_succ:
  forall v, wf (is_succ v) 0.
Proof.
  destruct v; steps.
Qed.

Hint Immediate wf_is_succ: wf.

Lemma wf_is_lambda:
  forall v, wf (is_lambda v) 0.
Proof.
  destruct v; steps.
Qed.

Hint Immediate wf_is_lambda: wf.

Lemma wf_smallstep:
  forall t1 t2,
    scbv_step t1 t2 ->
    wf t1 0 ->
    wf t2 0.
Proof.
  induction 1; steps; eauto using is_nat_value_build_nat with step_tactic wf.
Qed.

Hint Resolve wf_smallstep: wf.

Lemma wf_star_smallstep:
  forall t1 t2,
    star scbv_step t1 t2 ->
    wf t1 0 ->
    wf t2 0.
Proof.
  induction 1; steps; eauto using wf_smallstep.
Qed.

Hint Resolve wf_star_smallstep: wf.
