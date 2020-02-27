Require Export SystemFR.ShiftOpen.
Require Export SystemFR.EquivalentStar.

Opaque loop.

Lemma equivalent_context:
  forall C t1 t2,
    is_erased_term C ->
    wf C 1 ->
    pfv C term_var = nil ->
    equivalent_terms t1 t2 ->
    equivalent_terms (open 0 C t1) (open 0 C t2).
Proof.
  unfold equivalent_terms;
    steps;
    eauto with erased;
    eauto with wf;
    eauto with fv.

  - unshelve epose proof (H9 (shift_open 0 C0 C) _ _ _);
      repeat step || rewrite <- open_shift_open_zero in *;
      eauto with erased;
      eauto with wf;
      eauto with fv.

  - unshelve epose proof (H9 (shift_open 0 C0 C) _ _ _);
      repeat step || rewrite <- open_shift_open_zero in *;
      eauto with erased;
      eauto with wf;
      eauto with fv.
Qed.

Ltac equivalent_context C t1 t2 :=
  unshelve epose proof (equivalent_context C t1 t2 _ _ _ _).

Ltac equivalent_terms_ok :=
  unfold equivalent_terms in *; steps; eauto with wf.

Ltac find_context i :=
  match goal with
  | |- equivalent_terms (?F ?e1) (?F ?e2) =>
    equivalent_context (F (lvar i term_var)) e1 e2
  | |- equivalent_terms (?F ?e1 ?e) (?F ?e2 ?e) =>
    equivalent_context (F (lvar i term_var) e) e1 e2
  | |- equivalent_terms (?F ?e1 ?e ?e') (?F ?e2 ?e ?e') =>
    equivalent_context (F (lvar i term_var) e e') e1 e2
  end;
  repeat step || list_utils || rewrite open_none in * by equivalent_terms_ok;
    try solve [ equivalent_terms_ok ].

Lemma equivalent_tsize:
  forall e1 e2,
    equivalent_terms e1 e2 ->
    equivalent_terms (tsize e1) (tsize e2).
Proof.
  intros; find_context 0; steps.
Qed.

Lemma equivalent_app_left:
  forall e1 e2 e,
    is_erased_term e ->
    wf e 0 ->
    pfv e term_var = nil ->
    equivalent_terms e1 e2 ->
    equivalent_terms (app e1 e) (app e2 e).
Proof.
  intros; equivalent_context (app (lvar 0 term_var) e) e1 e2;
    repeat step || rewrite open_none in *;
    eauto with wf.
Qed.

Ltac find_middle_point :=
  match goal with
  | |- equivalent_terms (?F ?e1 ?e2) (?F ?e1' ?e2') =>
    apply equivalent_trans with (F e1 e2')
  | |- equivalent_terms (?F ?e1 ?e2 ?e) (?F ?e1' ?e2' ?e) =>
    apply equivalent_trans with (F e1 e2' e)
  | |- equivalent_terms (?F ?e1 ?e2 ?e3) (?F ?e1' ?e2' ?e3') =>
    apply equivalent_trans with (F e1 e2 e3')
  end.

Lemma equivalent_app:
  forall e1 e2 e1' e2',
    equivalent_terms e1 e1' ->
    equivalent_terms e2 e2' ->
    equivalent_terms (app e1 e2) (app e1' e2').
Proof.
  intros; find_middle_point; try solve [ find_context 0 ].
Qed.

Lemma equivalent_pp:
  forall e1 e2 e1' e2',
    equivalent_terms e1 e1' ->
    equivalent_terms e2 e2' ->
    equivalent_terms (pp e1 e2) (pp e1' e2').
Proof.
  intros; find_middle_point; try solve [ find_context 0 ].
Qed.

Lemma equivalent_left:
  forall e1 e2,
    equivalent_terms e1 e2 ->
    equivalent_terms (tleft e1) (tleft e2).
Proof.
  intros; find_context 0; steps.
Qed.

Lemma equivalent_right:
  forall e1 e2,
    equivalent_terms e1 e2 ->
    equivalent_terms (tright e1) (tright e2).
Proof.
  intros; find_context 0; steps.
Qed.

Lemma equivalent_succ:
  forall e1 e2,
    equivalent_terms e1 e2 ->
    equivalent_terms (succ e1) (succ e2).
Proof.
  intros; find_context 0; steps.
Qed.

Lemma equivalent_lambda:
  forall e1 e2,
    equivalent_terms e1 e2 ->
    equivalent_terms (notype_lambda e1) (notype_lambda e2).
Proof.
  intros; find_context 1; steps.
Qed.

Lemma equivalent_pi1:
  forall e1 e2,
    equivalent_terms e1 e2 ->
    equivalent_terms (pi1 e1) (pi1 e2).
Proof.
  intros; find_context 0; steps.
Qed.

Lemma equivalent_pi2:
  forall e1 e2,
    equivalent_terms e1 e2 ->
    equivalent_terms (pi2 e1) (pi2 e2).
Proof.
  intros; find_context 0; steps.
Qed.

Lemma equivalent_ite:
  forall e1 e2 e3 e1' e2' e3',
    equivalent_terms e1 e1' ->
    equivalent_terms e2 e2' ->
    equivalent_terms e3 e3' ->
    equivalent_terms (ite e1 e2 e3) (ite e1' e2' e3').
Proof.
  intros.
  find_middle_point; try solve [ find_context 0 ].
  find_middle_point; try solve [ find_context 0 ].
Qed.

Lemma equivalent_recognizer:
  forall e1 e2 r,
    equivalent_terms e1 e2 ->
    equivalent_terms (boolean_recognizer r e1) (boolean_recognizer r e2).
Proof.
  intros; find_context 0; steps.
Qed.

Lemma equivalent_fix:
  forall e1 e2,
    equivalent_terms e1 e2 ->
    equivalent_terms (notype_tfix e1) (notype_tfix e2).
Proof.
  intros; find_context 2; steps.
Qed.

Lemma equivalent_match:
  forall e1 e2 e3 e1' e2' e3',
    equivalent_terms e1 e1' ->
    equivalent_terms e2 e2' ->
    equivalent_terms e3 e3' ->
    equivalent_terms (tmatch e1 e2 e3) (tmatch e1' e2' e3').
Proof.
  intros.
  find_middle_point; try solve [ find_context 1 ].
  find_middle_point; try solve [ find_context 0 ].
Qed.

Lemma equivalent_sum_match:
  forall e1 e2 e3 e1' e2' e3',
    equivalent_terms e1 e1' ->
    equivalent_terms e2 e2' ->
    equivalent_terms e3 e3' ->
    equivalent_terms (sum_match e1 e2 e3) (sum_match e1' e2' e3').
Proof.
  intros.
  find_middle_point; try solve [ find_context 1 ].
  find_middle_point; try solve [ find_context 0 ]; try solve [ find_context 1 ].
Qed.

Lemma equivalent_value_pair:
  forall v1 v2 v',
    equivalent_terms (pp v1 v2) v' ->
    cbv_value v1 ->
    cbv_value v2 ->
    cbv_value v' ->
    exists v1' v2',
      cbv_value v1' /\
      cbv_value v2' /\
      equivalent_terms v1 v1' /\
      equivalent_terms v2 v2' /\
      v' = pp v1' v2'.
Proof.
  intros.
  unshelve epose proof (equivalent_context (pi1 (lvar 0 term_var)) _ _ _ _ _ H) as HH1;
    steps.
  unshelve epose proof (equivalent_context (pi2 (lvar 0 term_var)) _ _ _ _ _ H) as HH2;
    steps.
  eapply equivalent_normalizing in HH1;
    eauto using star_one with smallstep;
    repeat step || t_invert_star.
  eapply equivalent_normalizing in HH2;
    eauto using star_one with smallstep;
    repeat step || t_invert_star;
    eauto with step_tactic.
Qed.

Lemma equivalent_value_left:
  forall v v',
    equivalent_terms (tleft v) v' ->
    cbv_value v ->
    cbv_value v' ->
    exists v'',
      cbv_value v'' /\
      equivalent_terms v v'' /\
      v' = tleft v''.
Proof.
  intros.
  unshelve epose proof (equivalent_context (sum_match (lvar 0 term_var) (lvar 0 term_var) notype_err)
    _ _ _ _ _ H) as HH1;
    steps.
  unshelve epose proof (equivalent_normalizing _ _ v HH1 _ _);
    eauto using scbv_step_same, star_one with smallstep;
    repeat step || t_invert_star || step_inversion cbv_value;
    try solve [ eexists; steps ].
Qed.

Lemma equivalent_value_right:
  forall v v',
    equivalent_terms (tright v) v' ->
    cbv_value v ->
    cbv_value v' ->
    exists v'',
      cbv_value v'' /\
      equivalent_terms v v'' /\
      v' = tright v''.
Proof.
  intros.
  unshelve epose proof (equivalent_context (sum_match (lvar 0 term_var) notype_err (lvar 0 term_var))
    _ _ _ _ _ H) as HH1;
    steps.
  unshelve epose proof (equivalent_normalizing _ _ v HH1 _ _);
    eauto using scbv_step_same, star_one with smallstep;
    repeat step || t_invert_star || step_inversion cbv_value;
    try solve [ eexists; steps ].
Qed.

Lemma equivalent_beta:
  forall f t v,
    is_erased_term t ->
    is_erased_term f ->
    pfv t term_var = nil ->
    pfv f term_var = nil ->
    wf t 0 ->
    wf f 1 ->
    star scbv_step t v ->
    cbv_value v ->
    equivalent_terms (app (notype_lambda f) t) (open 0 f t).
Proof.
  intros.
  eapply equivalent_trans with (app (notype_lambda f) v);
    try solve [ equivalent_star ].
  eapply equivalent_trans with (open 0 f v);
    try solve [ equivalent_star ].

  apply equivalent_context; steps.
  apply equivalent_sym; equivalent_star.
Qed.
