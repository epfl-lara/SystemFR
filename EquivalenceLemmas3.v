Require Export SystemFR.StarInversions.
Require Export SystemFR.EquivalenceLemmas2.
Require Export SystemFR.EquivalentContext.

Lemma pp_pp_star_helper1:
  forall t1 t2,
    t1 ~>* t2 ->
    forall t1' t1'' t2' t2'',
      t1 = pp t1' t1'' ->
      t2 = pp t2' t2'' ->
      t1' ~>* t2'.
Proof.
  induction 1; repeat step || t_invert_step; eauto with star.
Qed.

Lemma pp_pp_star_1:
  forall t1 t1' t2 t2',
    pp t1 t1' ~>* pp t2 t2' ->
    t1 ~>* t2.
Proof. eauto using pp_pp_star_helper1. Qed.

Lemma pp_pp_star_helper2:
  forall t1 t2,
    t1 ~>* t2 ->
    forall t1' t1'' t2' t2'',
      t1 = pp t1' t1'' ->
      t2 = pp t2' t2'' ->
      t1'' ~>* t2''.
Proof.
  induction 1; repeat step || t_invert_step; eauto with star.
Qed.

Lemma pp_pp_star_2:
  forall t1 t1' t2 t2',
    pp t1 t1' ~>* pp t2 t2' ->
    t1' ~>* t2'.
Proof. eauto using pp_pp_star_helper2. Qed.

Lemma right_left_star_helper:
  forall t1 t2,
    t1 ~>* t2 ->
    forall t1' t2',
      t1 = tright t1' ->
      t2 = tleft t2' ->
      False.
Proof.
  induction 1; repeat step || t_invert_step; eauto.
Qed.

Lemma right_left_star:
  forall t1 t2,
    tright t1 ~>* tleft t2 ->
    False.
Proof.
  eauto using right_left_star_helper.
Qed.

Lemma right_right_star_helper:
  forall t1 t2,
    t1 ~>* t2 ->
    forall t1' t2',
      t1 = tright t1' ->
      t2 = tright t2' ->
      t1' ~>* t2'.
Proof.
  induction 1; repeat step || t_invert_step; eauto with star.
Qed.

Lemma right_right_star:
  forall t1 t2,
    tright t1 ~>* tright t2 ->
    t1 ~>* t2.
Proof.
  eauto using right_right_star_helper.
Qed.

Lemma left_left_star_helper:
  forall t1 t2,
    t1 ~>* t2 ->
    forall t1' t2',
      t1 = tleft t1' ->
      t2 = tleft t2' ->
      t1' ~>* t2'.
Proof.
  induction 1; repeat step || t_invert_step; eauto with star.
Qed.

Lemma left_left_star:
  forall t1 t2,
    tleft t1 ~>* tleft t2 ->
    t1 ~>* t2.
Proof.
  eauto using left_left_star_helper.
Qed.

Lemma equivalent_err:
  forall v,
    cbv_value v ->
    [ v ≡ notype_err ] ->
    False.
Proof.
  intros.
  equivalence_instantiate (app (notype_lambda ttrue) (lvar 0 term_var)); steps.
  unshelve epose proof (H3 _); eauto using scbv_step_same, star_one with smallstep;
    repeat step || t_invert_star || step_inversion cbv_value.
Qed.

Lemma right_left_equivalence:
  forall t v,
    cbv_value v ->
    [ tright t ≡ tleft v ] ->
    False.
Proof.
  intros.
  unshelve epose proof (equivalent_context (sum_match (lvar 0 term_var) ttrue notype_err)
  _ _ _ _ _ H0) as HH1; steps.
  apply equivalent_sym in HH1.
  unshelve epose proof (equivalent_normalizing _ _ ttrue HH1 _ _);
    repeat step || t_invert_star;
    eauto using scbv_step_same, star_one with smallstep values;
    eauto using right_left_star;
    eauto using equivalent_err with values.
Qed.

Lemma tright_equiv:
  forall t v,
    cbv_value v ->
    [ tright t ≡ tright v ] ->
    [ t ≡ v ].
Proof.
  intros.
  unshelve epose proof (equivalent_context (sum_match (lvar 0 term_var) notype_err (lvar 0 term_var))
  _ _ _ _ _ H0) as HH1; steps.
  apply equivalent_sym in HH1.
  unshelve epose proof (equivalent_normalizing _ _ v HH1 _ _);
    eauto using scbv_step_same, star_one with smallstep;
    repeat step || t_invert_star || step_inversion cbv_value;
    eauto with values;
    try solve [ eexists; steps ].

  eapply equivalent_trans; eauto using equivalent_sym.
  apply_anywhere right_right_star.
  apply equivalent_trans with v'; equivalent_star.
Qed.

Lemma tleft_equiv:
  forall t v,
    cbv_value v ->
    [ tleft t ≡ tleft v ] ->
    [ t ≡ v ].
Proof.
  intros.
  unshelve epose proof (equivalent_context (sum_match (lvar 0 term_var) (lvar 0 term_var) notype_err)
  _ _ _ _ _ H0) as HH1; steps.
  apply equivalent_sym in HH1.
  unshelve epose proof (equivalent_normalizing _ _ v HH1 _ _);
    eauto using scbv_step_same, star_one with smallstep;
    repeat step || t_invert_star || step_inversion cbv_value;
    eauto with values;
    try solve [ eexists; steps ].

  eapply equivalent_trans; eauto using equivalent_sym.
  apply_anywhere left_left_star.
  apply equivalent_trans with v'; equivalent_star.
Qed.

Lemma pair_equiv_1:
  forall t1 t2 v1 v2,
    [ pp t1 t2 ≡ pp v1 v2 ] ->
    cbv_value v1 ->
    cbv_value v2 ->
    [ t1 ≡ v1 ].
Proof.
  intros.
  unshelve epose proof (equivalent_context (pi1 (lvar 0 term_var)) _ _ _ _ _ H) as HH; steps.
  apply equivalent_sym in HH.
  unshelve epose proof (equivalent_normalizing _ _ v1 HH _ _);
    eauto using scbv_step_same, star_one with smallstep;
    repeat step || t_invert_star || step_inversion cbv_value;
    eauto with values;
    try solve [ eexists; steps ].
  eapply equivalent_trans; eauto using equivalent_sym; equivalent_star.
Qed.

Lemma pair_equiv_2:
  forall t1 t2 v1 v2,
    [ pp t1 t2 ≡ pp v1 v2 ] ->
    cbv_value v1 ->
    cbv_value v2 ->
    [ t2 ≡ v2 ].
Proof.
  intros.
  unshelve epose proof (equivalent_context (pi2 (lvar 0 term_var)) _ _ _ _ _ H) as HH; steps.
  apply equivalent_sym in HH.
  unshelve epose proof (equivalent_normalizing _ _ v2 HH _ _);
    eauto using scbv_step_same, star_one with smallstep;
    repeat step || t_invert_star || step_inversion cbv_value;
    eauto with values;
    try solve [ eexists; steps ].
  eapply equivalent_trans; eauto using equivalent_sym; equivalent_star.
Qed.
