Require Export SystemFR.LoopingTerm.

Lemma not_normalizing_loop:
  scbv_normalizing loop ->
  False.
Proof.
  unfold scbv_normalizing; steps; eauto using not_star_scbv_step_loop.
Qed.

Lemma r_normalizing_loop:
  scbv_normalizing loop <-> False.
Proof.
  steps; eauto using not_normalizing_loop.
Qed.

Opaque loop.

Lemma not_normalizing_err:
  scbv_normalizing notype_err ->
  False.
Proof.
  unfold scbv_normalizing; repeat step || t_invert_star || step_inversion cbv_value.
Qed.

Lemma r_normalizing_err:
  scbv_normalizing notype_err <-> False.
Proof.
  steps; eauto using not_normalizing_err.
Qed.

Lemma scbv_normalizing_ite_true:
  forall t1 t2,
    pfv t2 term_var = nil ->
    wf t2 0 ->
    scbv_normalizing (ite ttrue t1 t2) <-> scbv_normalizing t1.
Proof.
  unfold scbv_normalizing;
    repeat step || list_utils || t_invert_star; eauto with smallstep star.
Qed.

Lemma scbv_normalizing_ite_false:
  forall t1 t2,
    pfv t1 term_var = nil ->
    wf t1 0 ->
    scbv_normalizing (ite tfalse t1 t2) <-> scbv_normalizing t2.
Proof.
  unfold scbv_normalizing;
    repeat step || list_utils || t_invert_star; eauto with smallstep star.
Qed.

Lemma scbv_normalizing_zero:
  scbv_normalizing zero.
Proof.
  unfold scbv_normalizing; steps; eauto with smallstep values star.
Qed.

Lemma r_normalizing_zero:
  scbv_normalizing zero <-> True.
Proof.
  steps; eauto using scbv_normalizing_zero.
Qed.

Lemma scbv_normalizing_ttrue:
  scbv_normalizing ttrue.
Proof.
  unfold scbv_normalizing; steps; eauto with smallstep values star.
Qed.

Lemma r_normalizing_ttrue:
  scbv_normalizing ttrue <-> True.
Proof.
  steps; eauto using scbv_normalizing_ttrue.
Qed.

Lemma scbv_normalizing_step:
  forall t1 t2,
    scbv_normalizing t1 ->
    scbv_step t1 t2 ->
    scbv_normalizing t2.
Proof.
  unfold scbv_normalizing; steps.
  destruct H2; repeat step || t_nostep || t_deterministic_step;
    eauto.
Qed.

Lemma scbv_normalizing_back:
  forall t1 t2,
    scbv_normalizing t2 ->
    scbv_step t1 t2 ->
    scbv_normalizing t1.
Proof.
  unfold scbv_normalizing; steps; eauto with smallstep star.
Qed.
