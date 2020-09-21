Require Export SystemFR.StarInversions.
Require Export SystemFR.WFLemmas.

Require Import Psatz.

Definition loop: tree := notype_tfix (lvar 0 term_var).

Lemma wf_loop:
  forall k, wf loop k.
Proof.
  unfold loop; steps. try lia.
Qed.

Lemma pfv_loop:
  forall tag, pfv loop tag = nil.
Proof.
  unfold loop; steps.
Qed.

Lemma open_loop:
  forall k t, open k loop t = loop.
Proof.
  eauto using open_none, wf_loop.
Qed.

Lemma not_value_loop:
  cbv_value loop -> False.
Proof.
  unfold loop; repeat step || step_inversion cbv_value.
Qed.

Lemma not_value_app:
  forall t1 t2, cbv_value (app t1 t2) -> False.
Proof.
  unfold loop; repeat step || step_inversion cbv_value.
Qed.

Lemma scbv_step_loop:
  loop ~> loop.
Proof.
  unfold loop.
  eauto using scbv_step_same with smallstep.
Qed.

Lemma scbv_step_loop2:
  forall t,
    loop ~> t ->
    t = loop.
Proof.
  intros; eauto using deterministic_step, scbv_step_loop.
Qed.

Lemma not_star_scbv_step_loop':
  forall t v,
    t ~>* v ->
    t = loop ->
    cbv_value v ->
    False.
Proof.
  induction 1;
    repeat step || apply_anywhere scbv_step_loop2 || t_invert_step;
    eauto using not_value_loop;
    eauto using not_value_app.
Qed.

Lemma not_star_scbv_step_loop:
  forall v,
    loop ~>* v ->
    cbv_value v ->
    False.
Proof.
  eauto using not_star_scbv_step_loop'.
Qed.

Lemma is_erased_term_loop:
  is_erased_term loop.
Proof.
  unfold loop;
    steps.
Qed.
