Require Export SystemFR.Equivalence.
Require Export SystemFR.LoopingTerm.
Require Export SystemFR.CBVNormalizingLemmas.

Lemma equivalent_refl:
  forall t,
    is_erased_term t ->
    wf t 0 ->
    pfv t term_var = nil ->
    equivalent_terms t t.
Proof.
  unfold equivalent_terms; steps.
Qed.

Lemma equivalent_sym:
  forall t1 t2, equivalent_terms t1 t2 -> equivalent_terms t2 t1.
Proof.
  unfold equivalent_terms; steps; eauto with eapply_any.
Qed.

Lemma equivalent_trans:
  forall t1 t2 t3,
    equivalent_terms t1 t2 ->
    equivalent_terms t2 t3 ->
    equivalent_terms t1 t3
.
Proof.
  unfold equivalent_terms; steps; eauto 3 with apply_any.
  - apply H13; auto; apply H12; auto.
Qed.

Lemma equivalent_open:
  forall t1 k1 a1 t2 k2 a2,
    equivalent_terms t1 t2 ->
    equivalent_terms (open k1 t1 a1) (open k2 t2 a2).
Proof.
  unfold equivalent_terms;
    repeat step ||
           (rewrite (open_none t1) in * by eauto with wf lia) ||
           (rewrite (open_none t2) in * by eauto with wf lia);
    eauto with apply_any.
Qed.

Lemma equivalent_star_true:
  forall t1 t2,
    equivalent_terms t1 t2 ->
    star scbv_step t1 ttrue ->
    star scbv_step t2 ttrue.
Proof.
  intros.
  equivalence_instantiate (ite (lvar 0 term_var) uu loop);
    unfold scbv_normalizing in *; steps.
  unshelve epose proof (H3 (ex_intro _ uu _)); repeat step || t_invert_star;
    eauto using star_trans with smallstep cbvlemmas;
    eauto using not_star_scbv_step_loop with exfalso.
Qed.

Lemma equivalent_true:
  forall t,
    equivalent_terms t ttrue ->
    star scbv_step t ttrue.
Proof.
  intros; eauto using equivalent_star_true, equivalent_sym with star.
Qed.

Lemma equivalent_value_true:
  forall v,
    equivalent_terms v ttrue ->
    cbv_value v ->
    v = ttrue.
Proof.
  intros.
  apply_anywhere equivalent_true;
    repeat step || t_invert_star.
Qed.

Lemma false_true_not_equivalent:
  equivalent_terms tfalse ttrue ->
  False.
Proof.
  repeat step || apply_anywhere equivalent_true || t_invert_star.
Qed.

Lemma equivalent_star_false:
  forall t1 t2,
    equivalent_terms t1 t2 ->
    star scbv_step t1 tfalse ->
    star scbv_step t2 tfalse.
Proof.
  intros.
  equivalence_instantiate (ite (lvar 0 term_var) loop uu);
    unfold scbv_normalizing in *; steps.
  unshelve epose proof (H3 (ex_intro _ uu _)); repeat step || t_invert_star;
    eauto using star_trans with smallstep cbvlemmas;
    eauto using not_star_scbv_step_loop with exfalso.
Qed.

Lemma equivalent_false:
  forall t,
    equivalent_terms t tfalse ->
    star scbv_step t tfalse.
Proof.
  intros; eauto using equivalent_star_false, equivalent_sym with star.
Qed.

Lemma equivalent_value_false:
  forall v,
    equivalent_terms v tfalse ->
    cbv_value v ->
    v = tfalse.
Proof.
  intros.
  apply_anywhere equivalent_false;
    repeat step || t_invert_star.
Qed.

Ltac one_step_normalizing :=
  eapply scbv_normalizing_back; eauto with smallstep; steps;
    unfold scbv_normalizing; steps; eauto with star values.

Ltac not_normalizing :=
  top_level_unfold scbv_normalizing; repeat step || t_invert_star.

Lemma equivalent_value_unit:
  forall v,
    cbv_value v ->
    equivalent_terms uu v ->
    v = uu.
Proof.
  inversion 1;
    repeat step.

  - (* zero *)
    equivalence_instantiate (tmatch (lvar 0 term_var) uu uu); steps.
    unshelve epose proof (H4 _);
      try solve [ one_step_normalizing ];
      try solve [ not_normalizing ].

  - (* succ *)
    equivalence_instantiate (tmatch (lvar 0 term_var) uu uu); steps.
    unshelve epose proof (H5 _);
      try solve [ one_step_normalizing ];
      try solve [ not_normalizing ].

  - (* false *)
    equivalence_instantiate (ite (lvar 0 term_var) uu uu); steps.
    unshelve epose proof (H4 _);
      try solve [ one_step_normalizing ];
      try solve [ not_normalizing ].

  - (* true *)
    equivalence_instantiate (ite (lvar 0 term_var) uu uu); steps.
    unshelve epose proof (H4 _);
      try solve [ one_step_normalizing ];
      try solve [ not_normalizing ].

  - (* pair *)
    equivalence_instantiate (pi1 (lvar 0 term_var)); steps.
    unshelve epose proof (H6 _);
      try solve [ one_step_normalizing ];
      try solve [ not_normalizing ].

  - (* lambda *)
    equivalence_instantiate (ite (boolean_recognizer 2 (lvar 0 term_var)) uu loop);
      repeat step || rewrite open_loop in *; eauto using wf_loop.
    unshelve epose proof (H4 _).
    + eapply scbv_normalizing_back; eauto with smallstep; steps.
      eapply scbv_normalizing_back; eauto with smallstep; steps.
      unfold scbv_normalizing; steps; eauto with star values.

    + top_level_unfold scbv_normalizing; steps.
      force_invert (@star tree); repeat step || step_inversion cbv_value || step_inversion scbv_step.
      force_invert scbv_step; repeat step || t_invert_star;
        eauto using not_star_scbv_step_loop with exfalso.

  - (* left *)
    equivalence_instantiate (sum_match (lvar 0 term_var) uu uu); steps.
    unshelve epose proof (H5 _);
      try solve [ one_step_normalizing ];
      try solve [ not_normalizing ].

  - (* right *)
    equivalence_instantiate (sum_match (lvar 0 term_var) uu uu); steps.
    unshelve epose proof (H5 _);
      try solve [ one_step_normalizing ];
      try solve [ not_normalizing ].
Qed.

Lemma value_normalizing:
  forall v,
    cbv_value v ->
    scbv_normalizing v.
Proof.
  unfold scbv_normalizing; eauto with star.
Qed.
