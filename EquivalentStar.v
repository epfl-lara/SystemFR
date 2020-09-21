Require Export SystemFR.CBVNormalizingLemmas.
Require Export SystemFR.FVLemmasEval.
Require Export SystemFR.WFLemmasEval.
Require Export SystemFR.RewriteTactics.
Require Export SystemFR.EqualWithRelation.
Require Export SystemFR.TermLift.
Require Export SystemFR.EquivalenceLemmas.

Require Import Coq.Strings.String.
Require Import Psatz.
Require Import PeanoNat.

Opaque loop.
Opaque makeFresh.

Definition inter_reducible t1 t2: Prop :=
  wf t1 0 /\
  wf t2 0 /\
  is_erased_term t1 /\
  is_erased_term t2 /\
  (
    t1 ~>* t2 \/
    t2 ~>* t1
  ).

Lemma inter_reducible_open:
  forall t1 k1 a1 t2 k2 a2,
    inter_reducible t1 t2 ->
    inter_reducible (open k1 t1 a1) (open k2 t2 a2).
Proof.
  unfold inter_reducible;
    repeat step || (rewrite open_none in * by eauto with wf lia).
Qed.

Lemma star_inter_reducible:
  forall t1 t2,
    wf t1 0 ->
    is_erased_term t1 ->
    t1 ~>* t2 ->
    inter_reducible t1 t2.
Proof.
  unfold inter_reducible;
    steps; eauto with fv wf erased.
Qed.

Lemma star_lift_inter_reducible:
  forall t1 t2,
    is_erased_term t1 ->
    wf t1 0 ->
    t1 ~>* t2 ->
    term_lift inter_reducible t1 t2.
Proof.
  eauto using star_inter_reducible with term_lift.
Qed.

Lemma inter_reducible_sym:
  forall t1 t2,
    inter_reducible t1 t2 ->
    inter_reducible t2 t1.
Proof.
  unfold inter_reducible; steps.
Qed.

Lemma inter_reducible_refl:
  forall t,
    is_erased_term t ->
    wf t 0 ->
    inter_reducible t t.
Proof.
  unfold inter_reducible; steps.
Qed.

Lemma inter_reducible_step:
  forall t1 t1' t2,
    inter_reducible t1 t2 ->
    t1 ~> t1' ->
    inter_reducible t1' t2.
Proof.
  unfold inter_reducible;
    steps;
    eauto using star_trans with smallstep star;
    try solve [ eapply_anywhere star_one_step2; steps; eauto with smallstep star ];
    eauto with fv;
    eauto with wf;
    eauto with erased.
Qed.

Lemma inter_reducible_value:
  forall t v,
    inter_reducible t v ->
    cbv_value v ->
    t ~>* v.
Proof.
  induction 1;
    repeat step || t_invert_star.
Qed.

Lemma term_lift_inter_reducible_tsize:
  forall t v,
    term_lift inter_reducible t v ->
    ~ top_level_var v ->
    cbv_value v ->
    tsize t ~>* build_nat (tsize_semantics v).
Proof.
  induction 1;
    repeat step || step_inversion cbv_value || list_utils;
    eauto using scbv_step_same with star smallstep step_tactic;
    eauto 6 using inter_reducible_value, star_trans with cbvlemmas star smallstep.

  - repeat (eapply_anywhere star_smallstep_tsize_inv2; [
      idtac |
      solve [ eauto with values ] |
      solve [ eauto ]
    ]);
      repeat step || apply_anywhere build_nat_inj || rewrite_any.

    eapply star_trans; eauto with cbvlemmas.
    eapply star_trans; eauto with cbvlemmas.
    apply smallstep_star.
    eapply scbv_step_same.
    + apply SPBetaSize; repeat step || list_utils; eauto with values; eauto with fv.
    + steps.

  - repeat (eapply_anywhere star_smallstep_tsize_inv2; [
      idtac |
      solve [ eauto with values ] |
      solve [ eauto ]
    ]);
      repeat step || apply_anywhere build_nat_inj || rewrite_any.

    eapply star_trans; eauto with cbvlemmas.
    apply smallstep_star.
    eapply scbv_step_same.
    + apply SPBetaSize; repeat step || list_utils; eauto with values; eauto with fv.
    + steps.

  - repeat (eapply_anywhere star_smallstep_tsize_inv2; [
      idtac |
      solve [ eauto with values ] |
      solve [ eauto ]
    ]);
      repeat step || apply_anywhere build_nat_inj || rewrite_any.

    eapply star_trans; eauto with cbvlemmas.
    apply smallstep_star.
    eapply scbv_step_same.
    + apply SPBetaSize; repeat step || list_utils; eauto with values; eauto with fv.
    + steps.

  - repeat (eapply_anywhere star_smallstep_tsize_inv2; [
      idtac |
      solve [ eauto with values ] |
      solve [ eauto ]
    ]);
      repeat step || apply_anywhere build_nat_inj || rewrite_any.

    eapply star_trans; eauto with cbvlemmas.
    apply smallstep_star.
    eapply scbv_step_same.
    + apply SPBetaSize; repeat step || list_utils; eauto with values; eauto with fv.
    + steps.
Qed.

Lemma term_lift_inter_reducible_value:
  forall t v,
    term_lift inter_reducible t v ->
    cbv_value v ->
    exists v',
      t ~>* v' /\
      cbv_value v' /\
      term_lift inter_reducible v v'.
Proof.
  induction 1;
    repeat step || step_inversion cbv_value;
    try solve [ eexists; steps; eauto with smallstep star values; steps;
                eauto using term_lift_sym, inter_reducible_sym with term_lift ];
    try solve [ eexists; steps; eauto with cbvlemmas values term_lift ];
    try solve [ exists (pp v'0 v'); steps; eauto with cbvlemmas values term_lift ].

  eexists; steps; eauto using inter_reducible_value.
  unfold inter_reducible in *; steps; eauto using term_lift_refl.
Qed.

Ltac term_lift_inter_reducible_value :=
  match goal with
  | H: term_lift inter_reducible ?t ?v |- _ =>
    cbv_value v;
    poseNew (Mark H "lift_inter_reducible_value");
    unshelve epose proof (term_lift_inter_reducible_value t v H _)
  | H: term_lift inter_reducible ?v ?t |- _ =>
    cbv_value v;
    poseNew (Mark H "lift_inter_reducible_value");
    unshelve epose proof (term_lift_inter_reducible_value t v _ _)
  end.

Lemma term_lift_inter_reducible_lambda:
  forall t v,
    term_lift inter_reducible t v ->
    cbv_value v ->
    forall t0, t = notype_lambda t0 ->
    exists t0', v = notype_lambda t0' /\
      term_lift inter_reducible t0 t0'.
Proof.
  destruct 1;
    repeat step || step_inversion cbv_value; eauto.

  pose proof H as CH.
  apply_anywhere inter_reducible_value;
    repeat step || t_invert_star || top_level_unfold inter_reducible;
    eauto using term_lift_refl.
Qed.

Lemma term_lift_inter_reducible_pair:
  forall t v,
    term_lift inter_reducible t v ->
    cbv_value v ->
    wf t 0 ->
    wf v 0 ->
    is_erased_term t ->
    is_erased_term v ->
    forall t1 t2, t = pp t1 t2 ->
    exists v1 v2,
      v = pp v1 v2 /\
      term_lift inter_reducible t1 v1 /\
      term_lift inter_reducible t2 v2.
Proof.
  destruct 1;
    repeat step || step_inversion cbv_value || list_utils; eauto.

  apply_anywhere inter_reducible_value; repeat step || t_invert_star.
  eexists; eexists; steps;
    try solve [ constructor; unfold inter_reducible; steps; eauto with fv ].
Qed.

Lemma term_lift_inter_reducible_true:
  forall t v,
    term_lift inter_reducible t v ->
    t = ttrue ->
    cbv_value v ->
    v = ttrue.
Proof.
  destruct 1;
    repeat step || step_inversion cbv_value || list_utils; eauto.

  apply_anywhere inter_reducible_value; repeat step || t_invert_star.
Qed.

Lemma term_lift_inter_reducible_false:
  forall t v,
    term_lift inter_reducible t v ->
    t = tfalse ->
    cbv_value v ->
    v = tfalse.
Proof.
  destruct 1;
    repeat step || step_inversion cbv_value || list_utils; eauto.

  apply_anywhere inter_reducible_value; repeat step || t_invert_star.
Qed.

Lemma term_lift_inter_reducible_zero:
  forall t v,
    term_lift inter_reducible t v ->
    t = zero ->
    cbv_value v ->
    v = zero.
Proof.
  destruct 1;
    repeat step || step_inversion cbv_value || list_utils; eauto.

  apply_anywhere inter_reducible_value; repeat step || t_invert_star.
Qed.

Lemma term_lift_inter_reducible_succ:
  forall t v,
    term_lift inter_reducible t v ->
    cbv_value v ->
    wf t 0 ->
    wf v 0 ->
    is_erased_term t ->
    is_erased_term v ->
    forall t', t = succ t' ->
    exists v',
      v = succ v' /\
      term_lift inter_reducible t' v'.
Proof.
  destruct 1;
    repeat step || step_inversion cbv_value || list_utils; eauto.

  apply_anywhere inter_reducible_value; repeat step || t_invert_star.
  eexists; steps;
    try solve [ constructor; unfold inter_reducible; steps; eauto with fv ].
Qed.

Lemma term_lift_inter_reducible_left:
  forall t v,
    term_lift inter_reducible t v ->
    cbv_value v ->
    wf t 0 ->
    wf v 0 ->
    is_erased_term t ->
    is_erased_term v ->
    forall t', t = tleft t' ->
    exists v',
      v = tleft v' /\
      term_lift inter_reducible t' v'.
Proof.
  destruct 1;
    repeat step || step_inversion cbv_value || list_utils; eauto.

  apply_anywhere inter_reducible_value; repeat step || t_invert_star.
  eexists; steps;
    try solve [ constructor; unfold inter_reducible; steps; eauto with fv ].
Qed.

Lemma term_lift_inter_reducible_right:
  forall t v,
    term_lift inter_reducible t v ->
    cbv_value v ->
    wf t 0 ->
    wf v 0 ->
    is_erased_term t ->
    is_erased_term v ->
    forall t', t = tright t' ->
    exists v',
      v = tright v' /\
      term_lift inter_reducible t' v'.
Proof.
  destruct 1;
    repeat step || step_inversion cbv_value || list_utils; eauto.

  apply_anywhere inter_reducible_value; repeat step || t_invert_star.
  eexists; steps;
    try solve [ constructor; unfold inter_reducible; steps; eauto with fv ].
Qed.

Ltac invert_lift :=
  match goal with
  | H: term_lift inter_reducible ?t1 ?t2 |- _ =>
    is_var t2; not_var t1; inversion H; clear H
  end.

Lemma term_lift_inter_reducible_open:
  forall t1 t2,
    term_lift inter_reducible t1 t2 ->
    forall t1' t2' k,
      term_lift inter_reducible t1' t2' ->
      term_lift inter_reducible (open k t1 t1') (open k t2 t2')
.
Proof.
  induction 1;
    repeat step || top_level_unfold inter_reducible ||
           (rewrite open_none in * by eauto 2 with wf lia);
    try solve [ constructor; unfold inter_reducible; steps ].
Qed.

Lemma term_lift_inter_reducible_topen:
  forall T T',
    term_lift inter_reducible T T' ->
    forall k X X',
      term_lift inter_reducible X X' ->
      term_lift inter_reducible (topen k T X) (topen k T' X').
Proof.
  induction 1; repeat step;
    eauto 6 with term_lift;
    try solve [
      top_level_unfold inter_reducible; repeat step || rewrite topen_none by eauto with twf;
        eauto using star_lift_inter_reducible, term_lift_sym, inter_reducible_sym
    ].
Qed.

Lemma term_lift_inter_reducible_is_pair:
  forall v1 v2,
    term_lift inter_reducible v1 v2 ->
    cbv_value v1 ->
    cbv_value v2 ->
    is_pair v1 = is_pair v2.
Proof.
  induction 1;
    repeat step || unfold inter_reducible in * || t_invert_star.
Qed.

Lemma term_lift_inter_reducible_is_lambda:
  forall v1 v2,
    term_lift inter_reducible v1 v2 ->
    cbv_value v1 ->
    cbv_value v2 ->
    is_lambda v1 = is_lambda v2.
Proof.
  induction 1;
    repeat step || unfold inter_reducible in * || t_invert_star.
Qed.

Lemma term_lift_inter_reducible_is_succ:
  forall v1 v2,
    term_lift inter_reducible v1 v2 ->
    cbv_value v1 ->
    cbv_value v2 ->
    is_succ v1 = is_succ v2.
Proof.
  induction 1;
    repeat step || unfold inter_reducible in * || t_invert_star.
Qed.

Lemma inter_reducible_values:
  forall v1 v2,
    inter_reducible v1 v2 ->
    cbv_value v1 ->
    cbv_value v2 ->
    v1 = v2.
Proof.
  unfold inter_reducible;
    repeat step || t_invert_star.
Qed.

Lemma term_lift_inter_reducible_top_level_var:
  forall v1 v2,
    term_lift inter_reducible v1 v2 ->
    cbv_value v1 ->
    cbv_value v2 ->
    top_level_var v1 ->
    top_level_var v2.
Proof.
  induction 1;
    repeat step || step_inversion cbv_value;
    try solve [ apply_anywhere inter_reducible_values; steps ].
Qed.

Lemma term_lift_inter_reducible_top_level_var2:
  forall v1 v2,
    term_lift inter_reducible v1 v2 ->
    cbv_value v1 ->
    cbv_value v2 ->
    top_level_var v2 ->
    top_level_var v1.
Proof.
  induction 1;
    repeat step || step_inversion cbv_value;
    try solve [ apply_anywhere inter_reducible_values; steps ].
Qed.

Lemma term_lift_inter_reducible_step:
  forall t1 t2,
    term_lift inter_reducible t1 t2 ->
    wf t1 0 ->
    wf t2 0 ->
    is_erased_term t1 ->
    is_erased_term t2 ->
    forall t1', t1 ~> t1' ->
    exists t2',
      term_lift inter_reducible t1' t2' /\
      t2 ~>* t2'.
Proof.
  induction 1;
    repeat step || t_invert_step || instantiate_any || list_utils;
    eauto using inter_reducible_step with star smallstep term_lift;
    eauto with cbvlemmas term_lift.

  - eexists; steps; eauto using term_lift_inter_reducible_tsize, term_lift_sym, inter_reducible_sym.
    apply term_lift_refl; eauto with erased.

  - repeat term_lift_inter_reducible_value; steps;
      eauto with values;
      eauto using term_lift_sym, inter_reducible_sym.

    eapply term_lift_inter_reducible_lambda in H18; steps.
    exists (open 0 t0' v'0); steps; eauto 7 using star_trans with cbvlemmas smallstep;
      eauto using term_lift_inter_reducible_open.

  - repeat term_lift_inter_reducible_value; steps;
      eauto with values;
      eauto using term_lift_sym, inter_reducible_sym.

    exists (app v' t2'0); steps; eauto using star_trans with cbvlemmas; eauto with term_lift.

  - repeat term_lift_inter_reducible_value; steps;
      eauto with values;
      eauto using term_lift_sym, inter_reducible_sym.

    exists (pp v' t2'0); steps; eauto using star_trans with cbvlemmas; eauto with term_lift.

  - repeat term_lift_inter_reducible_value; steps;
      eauto with values;
      eauto using term_lift_sym, inter_reducible_sym.

    eapply term_lift_inter_reducible_pair in H13; repeat step || list_utils || step_inversion cbv_value;
      eauto with fv; eauto with wf; eauto with erased;
      eauto 7 using star_trans with cbvlemmas smallstep.

  - repeat term_lift_inter_reducible_value; steps;
      eauto with values;
      eauto using term_lift_sym, inter_reducible_sym.

    eapply term_lift_inter_reducible_pair in H13; repeat step || list_utils || step_inversion cbv_value;
      eauto with fv; eauto with wf; eauto with erased;
      eauto 7 using star_trans with cbvlemmas smallstep.

  - repeat term_lift_inter_reducible_value; steps;
      eauto with values;
      eauto using term_lift_sym, inter_reducible_sym.

    eapply term_lift_inter_reducible_true in H20; steps;
      eauto 6 using star_trans with cbvlemmas smallstep.

  - repeat term_lift_inter_reducible_value; steps;
      eauto with values;
      eauto using term_lift_sym, inter_reducible_sym.

    eapply term_lift_inter_reducible_false in H20; steps;
      eauto 6 using star_trans with cbvlemmas smallstep.

  - repeat term_lift_inter_reducible_value; steps;
      eauto with values;
      eauto using term_lift_sym, inter_reducible_sym.

    exists (is_pair t); steps; eauto using term_lift_refl with erased.

    erewrite term_lift_inter_reducible_is_pair by eauto.
    eapply star_trans; eauto with cbvlemmas.
    apply star_one; constructor; steps; eauto using term_lift_inter_reducible_top_level_var2.

  - repeat term_lift_inter_reducible_value; steps;
      eauto with values;
      eauto using term_lift_sym, inter_reducible_sym.

    exists (is_succ t); steps; eauto using term_lift_refl with erased.

    erewrite term_lift_inter_reducible_is_succ by eauto.
    eapply star_trans; eauto with cbvlemmas.
    apply star_one; constructor; steps; eauto using term_lift_inter_reducible_top_level_var2.

  - repeat term_lift_inter_reducible_value; steps;
      eauto with values;
      eauto using term_lift_sym, inter_reducible_sym.

    exists (is_lambda t); steps; eauto using term_lift_refl with erased.

    erewrite term_lift_inter_reducible_is_lambda by eauto.
    eapply star_trans; eauto with cbvlemmas.
    apply star_one; constructor; steps; eauto using term_lift_inter_reducible_top_level_var2.

  - repeat term_lift_inter_reducible_value; steps;
      eauto with values;
      eauto using term_lift_sym, inter_reducible_sym.

    eapply term_lift_inter_reducible_zero in H19; steps;
      eauto 6 using star_trans with cbvlemmas smallstep.

  - repeat term_lift_inter_reducible_value; steps;
      eauto with values;
      eauto using term_lift_sym, inter_reducible_sym.

    eapply term_lift_inter_reducible_succ in H20; repeat step || step_inversion cbv_value;
      eauto 6 using star_trans with cbvlemmas smallstep;
      eauto with fv; eauto with wf; eauto with erased.

    exists (open 0 t3' v'0);
      steps;
      eauto using term_lift_inter_reducible_open with term_lift;
      eauto 6 using star_trans with cbvlemmas smallstep.

  - exists (open 0 (open 1 t' zero) (notype_tfix t'));
      steps;
      eauto using term_lift_inter_reducible_open with term_lift;
      eauto 6 using star_trans with cbvlemmas smallstep.

  - repeat term_lift_inter_reducible_value; steps;
      eauto with values;
      eauto using term_lift_sym, inter_reducible_sym.

    eapply term_lift_inter_reducible_left in H19; repeat step || step_inversion cbv_value;
      eauto 6 using star_trans with cbvlemmas smallstep;
      eauto with fv; eauto with wf; eauto with erased.

    exists (open 0 t2' v'0);
      steps;
      eauto using term_lift_inter_reducible_open with term_lift;
      eauto 6 using star_trans with cbvlemmas smallstep.

  - repeat term_lift_inter_reducible_value; steps;
      eauto with values;
      eauto using term_lift_sym, inter_reducible_sym.

    eapply term_lift_inter_reducible_right in H19; repeat step || step_inversion cbv_value;
      eauto 6 using star_trans with cbvlemmas smallstep;
      eauto with fv; eauto with wf; eauto with erased.

    exists (open 0 t3' v'0);
      steps;
      eauto using term_lift_inter_reducible_open with term_lift;
      eauto 6 using star_trans with cbvlemmas smallstep.
Qed.

Lemma term_lift_inter_reducible_star:
  forall t1 t1',
    t1 ~>* t1' ->
    forall t2,
      term_lift inter_reducible t1 t2 ->
      wf t1 0 ->
      wf t2 0 ->
      is_erased_term t1 ->
      is_erased_term t2 ->
      exists t2',
        term_lift inter_reducible t1' t2' /\
        t2 ~>* t2'.
Proof.
  induction 1; steps;
    eauto using term_lift_refl with star.

  unshelve epose proof (term_lift_inter_reducible_step _ _ H1 _ _ _ _ _ H);
    eauto; repeat step || instantiate_any.

  unshelve epose proof (H9 _ _ _ _);
    eauto with wf;
    eauto with fv;
    eauto with erased;
    steps;
    eauto using star_trans.
Qed.

Lemma term_lift_inter_reducible_normalizing:
  forall t1 t2,
    scbv_normalizing t1 ->
    term_lift inter_reducible t1 t2 ->
    wf t1 0 ->
    wf t2 0 ->
    is_erased_term t1 ->
    is_erased_term t2 ->
    scbv_normalizing t2.
Proof.
  unfold scbv_normalizing; steps.
  unshelve epose proof (term_lift_inter_reducible_star _ _ H6 _ H0 _ _ _ _);
    steps.
  term_lift_inter_reducible_value; steps; eauto using term_lift_sym, inter_reducible_sym;
    eauto using star_trans.
Qed.

Lemma term_lift_inter_reducible_equivalent:
  forall t1 t2,
    term_lift inter_reducible t1 t2 ->
    wf t1 0 ->
    wf t2 0 ->
    is_erased_term t1 ->
    is_erased_term t2 ->
    pfv t1 term_var = nil ->
    pfv t2 term_var = nil ->
    [ t1 ≡ t2 ].
Proof.
  unfold equivalent_terms;
    steps;
    eauto with erased wf fv.

  - unshelve epose proof (term_lift_inter_reducible_star _ _ H9 (open 0 C t2) _ _ _ _ _);
      repeat step;
      eauto with wf erased;
      eauto using term_lift_inter_reducible_open, term_lift_refl.

    term_lift_inter_reducible_value; steps; eauto using inter_reducible_sym, term_lift_sym.
    apply_anywhere term_lift_inter_reducible_true; steps; eauto using star_trans.

  - unshelve epose proof (term_lift_inter_reducible_star _ _ H9 (open 0 C t1) _ _ _ _ _);
      repeat step;
      eauto with wf erased;
      eauto using term_lift_inter_reducible_open, term_lift_refl, term_lift_sym, inter_reducible_sym.

    term_lift_inter_reducible_value; steps; eauto using inter_reducible_sym, term_lift_sym.
    apply_anywhere term_lift_inter_reducible_true; steps; eauto using star_trans.
Qed.

Lemma equivalent_star:
  forall t1 t2,
    is_erased_term t1 ->
    wf t1 0 ->
    pfv t1 term_var = nil ->
    t1 ~>* t2 ->
    [ t1 ≡ t2 ].
Proof.
  intros.
  apply term_lift_inter_reducible_equivalent; steps; eauto with wf erased fv.
  constructor.
  unfold inter_reducible;
    repeat step; eauto with wf erased.
Qed.

Ltac equivalent_star :=
  apply equivalent_star; repeat step || list_utils;
    try solve [
      unfold equivalent_terms in *; repeat step || list_utils;
      t_closer
    ];
    eauto using star_trans with cbvlemmas smallstep values.

Lemma term_lift_inter_reducible_size:
  forall T1 T2,
    term_lift inter_reducible T1 T2 ->
    type_nodes T1 = type_nodes T2.
Proof.
  induction 1;
    repeat step || unfold inter_reducible in * || rewrite type_nodes_term in * by auto.
Qed.

Lemma equivalent_normalizing:
  forall t1 t2 v1,
   [ t1 ≡ t2 ] ->
   t1 ~>* v1 ->
   cbv_value v1 ->
   exists v2,
     [ v1 ≡ v2 ] /\
     t2 ~>* v2 /\
     cbv_value v2
.
Proof.
  intros.
  equivalence_instantiate (app (notype_lambda ttrue) (lvar 0 term_var));
    steps.

  unshelve epose proof (H4 _);
    eauto 6 using star_one, scbv_step_same, star_trans with values smallstep cbvlemmas;
    repeat step || t_invert_star.

  eexists; steps; try eassumption.

  eapply equivalent_square; eauto;
    try solve [ equivalent_star ].
Qed.

Ltac equivalent_normalizing :=
  match goal with
  | H1: [ ?t1 ≡ ?t2 ],
    H2: ?t1 ~>* ?v1 |- _ =>
    poseNew (Mark (H1, H2) "equivalent_normalizing");
    unshelve epose proof (equivalent_normalizing _ _ _ H1 H2 _)
  end.

Lemma equivalent_value:
  forall t v,
   [ t ≡ v ] ->
   cbv_value v ->
   exists v',
     [ v' ≡ v ] /\
     t ~>* v' /\
     cbv_value v'
.
Proof.
  intros.
  unshelve epose proof (equivalent_normalizing v t v _ _ H0);
    repeat step;
    eauto using equivalent_sym.
Qed.

Ltac equivalent_value :=
  match goal with
  | H: [ ?t ≡ ?v ] |- _ =>
    cbv_value v;
    not_cbv_value t;
    poseNew (Mark (t, v) "equivalent_value");
    unshelve epose proof (equivalent_value _ _ H _)
  | H: [ ?v ≡ ?t ] |- _ =>
    cbv_value v;
    not_cbv_value t;
    poseNew (Mark (t, v) "equivalent_value");
    unshelve epose proof (equivalent_value t v _ _)
  end.
