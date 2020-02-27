Require Export SystemFR.WFLemmas.
Require Export SystemFR.SmallStep.
Require Export SystemFR.SizeLemmas.
Require Export SystemFR.PrimitiveRecognizers.
Require Export SystemFR.RelationClosures.

Lemma wf_nat_value:
  forall v k, is_nat_value v -> wf v k.
Proof.
  induction 1; steps.
Qed.

Hint Immediate wf_nat_value: wf.

Lemma twf_nat_value:
  forall v k, is_nat_value v -> twf v k.
Proof.
  induction 1; steps.
Qed.

Hint Immediate twf_nat_value: twf.

Lemma wf_is_pair:
  forall v k, wf (is_pair v) k.
Proof.
  destruct v; steps.
Qed.

Hint Immediate wf_is_pair: wf.

Lemma wf_is_succ:
  forall v k, wf (is_succ v) k.
Proof.
  destruct v; steps.
Qed.

Hint Immediate wf_is_succ: wf.

Lemma wf_is_lambda:
  forall v k, wf (is_lambda v) k.
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

Hint Immediate wf_smallstep: wf.

Lemma wf_star_smallstep:
  forall t1 t2,
    star scbv_step t1 t2 ->
    wf t1 0 ->
    wf t2 0.
Proof.
  induction 1; steps; eauto using wf_smallstep.
Qed.

Hint Immediate wf_star_smallstep: wf.

Lemma open_is_nat_value_wf:
  forall v i j rep,
    is_nat_value v ->
    wf rep 0 ->
    wf (open i v rep) j.
Proof.
  induction 1; steps.
Qed.

Hint Immediate open_is_nat_value_wf: wf.
