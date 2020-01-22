Require Import Coq.Strings.String.

Require Export SystemFR.EquivalentStar.

Definition tlt (a: tree) (b: tree) :=
  app
    (notype_rec a
      (notype_lambda (tmatch (lvar 0 term_var) tfalse ttrue))
      (notype_lambda (tmatch (lvar 0 term_var) tfalse (app (app (lvar 2 term_var) uu) (lvar 0 term_var)))))
    b.

Lemma tlt_def:
  forall a b,
    app
      (notype_rec a
        (notype_lambda (tmatch (lvar 0 term_var) tfalse ttrue))
        (notype_lambda (tmatch (lvar 0 term_var) tfalse (app (app (lvar 2 term_var) uu) (lvar 0 term_var)))))
      b = tlt a b.
Proof.
  reflexivity.
Qed.

Lemma tlt_a_zero:
  forall a,
    star scbv_step (tlt a zero) ttrue ->
    False.
Proof.
  unfold tlt in *;
    repeat step || t_invert_star || star_smallstep_app_onestep || step_inversion cbv_value.
Qed.

Lemma tlt_zero_b:
  forall b,
    cbv_value b ->
    star scbv_step (tlt zero b) ttrue ->
    1 <= tree_size b.
Proof.
  destruct 1; repeat step;
    eauto with omega;
    try solve [ inversion H; unfold tlt in *;
      repeat step || t_invert_step || star_smallstep_app_onestep || t_invert_star
    ].
Qed.

Lemma open_is_nat_value_wf:
  forall v i j rep,
    is_nat_value v ->
    wf rep 0 ->
    wf (open i v rep) j.
Proof.
  induction 1; steps.
Qed.

Hint Immediate open_is_nat_value_wf: wf.

Ltac reverse_once :=
  t_invert_star; repeat step || star_smallstep_value || step_inversion cbv_value || star_smallstep_app_onestep.

Lemma tlt_something:
  forall a b,
    cbv_value a ->
    cbv_value b ->
    star scbv_step (tlt a b) ttrue ->
    exists b', b = succ b' /\
      (a = zero \/ exists a', a = succ a').
Proof.
  unfold tlt; steps.
  reverse_once; reverse_once; reverse_once; eauto.
Qed.

Lemma tlt_succ:
  forall a b,
    cbv_value a ->
    cbv_value b ->
    wf a 0 ->
    star scbv_step (tlt (succ a) (succ b)) ttrue ->
    star scbv_step (tlt a b) ttrue.
Proof.
  unfold tlt; steps.

  reverse_once; eauto with values.
  reverse_once; eauto with values.
  reverse_once; eauto with values.
  reverse_once; eauto with values.

  repeat rewrite (open_none a) in * by eauto with wf;
    eauto using star_trans with cbvlemmas.
Qed.

Lemma tlt_sound:
  forall a, cbv_value a ->
    wf a 0 ->
    forall b, cbv_value b ->
    star scbv_step (tlt a b) ttrue ->
    tree_size a < tree_size b.
Proof.
  induction 1; steps; eauto using tlt_zero_b; eauto with lia;
    try solve [ apply_anywhere tlt_something; steps; eauto with values ].

  destruct H1; steps;
    try solve [ apply_anywhere tlt_something; steps; eauto with values ];
    eauto using le_n_S, tlt_succ.
Qed.

Ltac t_tlt_sound :=
  match goal with
  | H: star scbv_step (tlt ?a ?b) ttrue |- _ =>
    cbv_value a; cbv_value b;
    poseNew (Mark (a,b) "tlt_sound");
    unshelve epose proof (tlt_sound a _ _ b _ H)
  | H: equivalent_terms (tlt ?a ?b) ttrue |- _ =>
    cbv_value a; cbv_value b;
    poseNew (Mark (a,b) "tlt_sound");
    unshelve epose proof (tlt_sound a _ _ b _ _)
  end.

Lemma open_tlt:
  forall a b k rep, open k (tlt a b) rep = tlt (open k a rep) (open k b rep).
Proof.
  unfold tlt; repeat step.
Qed.

Lemma pfv_tlt:
  forall a b tag, pfv (tlt a b) tag = pfv a tag ++ pfv b tag.
Proof.
  unfold tlt; repeat step || rewrite List.app_nil_r in *.
Qed.

Lemma psubstitute_tlt:
  forall a b l tag,
    psubstitute (tlt a b) l tag = tlt (psubstitute a l tag) (psubstitute b l tag).
Proof.
  unfold tlt; repeat step.
Qed.

Ltac one_step_aux :=
 eapply Trans; [ eauto using is_nat_value_build_nat with values smallstep cbvlemmas | idtac ];
   repeat step || (rewrite open_none in * by (repeat step; eauto using is_nat_value_build_nat with wf)).

Ltac one_step := unshelve one_step_aux; steps.

Lemma tlt_complete:
  forall a b,
    a < b ->
    star scbv_step (tlt (build_nat a) (build_nat b)) ttrue.
Proof.
  unfold tlt; induction a; destruct b; repeat step || eauto with omega || one_step.
Qed.

Lemma is_nat_value_buildable:
  forall v, is_nat_value v ->
    exists n, v = build_nat n.
Proof.
  induction 1; steps.
  - exists 0; steps.
  - exists (S n); steps.
Qed.

Ltac t_is_nat_value_buildable :=
  match goal with
  | H: is_nat_value ?v |- _ =>
    poseNew (Mark v "is_nat_value_buildable");
    pose proof (is_nat_value_buildable v H)
  end.

Lemma tree_size_build_nat:
  forall n, tree_size (build_nat n) = n.
Proof.
  induction n; steps.
Qed.

Lemma tlt_complete2:
  forall a b,
    is_nat_value a ->
    is_nat_value b ->
    tree_size a < tree_size b ->
    star scbv_step (tlt a b) ttrue.
Proof.
  repeat step || t_is_nat_value_buildable || apply tlt_complete || rewrite tree_size_build_nat in *.
Qed.

Lemma true_is_irred: irred ttrue.
Proof.
  unfold irred; repeat step || t_nostep.
Qed.

Lemma equivalent_tlt_steps:
  forall t1 t2 v1 v2,
    equivalent_terms (tlt t1 t2) ttrue ->
    star scbv_step t1 v1 ->
    star scbv_step t2 v2 ->
    is_nat_value v1 ->
    is_nat_value v2 ->
    equivalent_terms (tlt v1 v2) ttrue.
Proof.
  unfold tlt; intros.
  apply equivalent_star; repeat step || list_utils; eauto with erased wf fv.
  apply equivalent_true in H; steps.
  apply (star_many_steps _ (app
           (notype_rec v1 (notype_lambda (tmatch (lvar 0 term_var) tfalse ttrue))
              (notype_lambda
                 (tmatch (lvar 0 term_var) tfalse (app (app (lvar 2 term_var) uu) (lvar 0 term_var)))))
           t2)) in H; eauto with cbvlemmas; repeat step || unfold irred || t_nostep.
  inversion H; repeat step || t_invert_step || t_nostep || step_inversion cbv_value.

  - eapply Trans; eauto with smallstep; steps.
    eapply star_many_steps; eauto with cbvlemmas values; eauto using true_is_irred.
  - eapply Trans; eauto with smallstep; steps.
    eapply star_many_steps; eauto with cbvlemmas values; eauto using true_is_irred.
Qed.

Lemma is_erased_term_tlt:
  forall t1 t2,
    is_erased_term t1 ->
    is_erased_term t2 ->
    is_erased_term (tlt t1 t2).
Proof.
  unfold tlt; steps.
Qed.

Lemma wf_tlt:
  forall t1 t2 k,
    wf t1 k ->
    wf t2 k ->
    wf (tlt t1 t2) k.
Proof.
  unfold tlt; steps; eauto with lia.
Qed.

Lemma star_smallstep_tlt_left:
  forall t1 t2 t,
    star scbv_step t1 t2 ->
    star scbv_step (tlt t1 t) (tlt t2 t).
Proof.
  unfold tlt; steps; eauto with cbvlemmas.
Qed.
