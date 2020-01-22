Require Export SystemFR.LoopingTerm.

Opaque loop.

Fixpoint nat_recognizer (v: tree): tree :=
  match v with
  | zero => tmatch (lvar 0 term_var) uu loop
  | succ v' => tmatch (lvar 0 term_var) loop (nat_recognizer v')
  | _ => uu
  end.

Lemma is_erased_term_nat_recognizer:
  forall v, is_erased_term (nat_recognizer v).
Proof.
  induction v;
    repeat step.
Qed.

Lemma wf_nat_recognizer:
  forall v, wf (nat_recognizer v) 1.
Proof.
  induction v;
    repeat step; eauto with wf; eauto using wf_loop.
Qed.

Lemma fv_nat_recognizer:
  forall v tag, pfv (nat_recognizer v) tag = nil.
Proof.
  induction v;
    repeat step || list_utils.
Qed.

Lemma eval_nat_recognizer:
  forall v,
    is_nat_value v ->
    star scbv_step (open 0 (nat_recognizer v) v) uu.
Proof.
  induction 1;
    repeat step; eauto using star_one with smallstep.

  eapply Trans; eauto with smallstep values.
  rewrite (open_none _ 1); eauto using wf_nat_recognizer.
Qed.

Lemma normalizing_nat_recognizer:
  forall v,
    is_nat_value v ->
    forall v',
      cbv_value v' ->
      scbv_normalizing (open 0 (nat_recognizer v) v') ->
      v = v'
.
Proof.
  induction 1;
    repeat step; eauto using star_one with smallstep.

  - unfold scbv_normalizing in *; repeat step || t_invert_star || rewrite open_loop in *;
      eauto using not_star_scbv_step_loop with exfalso.

  - unfold scbv_normalizing in *;
      repeat step || t_invert_star || rewrite open_loop in *;
      eauto using not_star_scbv_step_loop with exfalso.

    clear_marked.
    rewrite (open_none _ 1) in H7 by eauto using wf_nat_recognizer.
    unshelve epose proof (IHis_nat_value v'0 _ _); steps; eauto.
Qed.
