Require Import SystemFR.Trees.
Require Import SystemFR.Syntax.
Require Import SystemFR.StarInversions.
Require Import SystemFR.StarRelation.
Require Import SystemFR.StarLemmas.
Require Import SystemFR.SmallStep.
Require Import SystemFR.Tactics.
Require Import SystemFR.WFLemmas.

Require Import SystemFR.WFLemmasEval.
Require Import SystemFR.TermProperties.

Require Import SystemFR.Equivalence.
Require Import SystemFR.EquivalenceLemmas.

Require Import Coq.Strings.String.

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

Ltac t_invert_app :=
  match goal with
  | H2: star small_step (app ?t1 ?t2) ?v |- _ =>
    poseNew (Mark H2 "inv app");
    unshelve epose proof (star_smallstep_app_inv _ v H2 _ t1 t2 eq_refl)
  end.

Ltac t_invert_match_zero :=
  match goal with
  | H1: is_value ?v,
    H2: star small_step (tmatch zero _ _) ?v |- _ =>
    poseNew (Mark H2 "inv match zero2");
    unshelve epose proof (star_smallstep_match_zero _ v H2 H1 _ _ _ eq_refl _)
  end.

Ltac t_star_smallstep_app_onestep :=
  match goal with
  | H: star small_step (app (notype_lambda ?t) ?v1) ?v2 |- _ =>
    poseNew (Mark H "star_smallstep_app_onestep");
    unshelve epose proof (star_smallstep_app_onestep _ _ _ H _ _)
  end.

Lemma tlt_a_zero:
  forall a,
    is_nat_value a ->
    star small_step (tlt a zero) ttrue ->
    False.
Proof.
  assert (is_value ttrue); steps.
  unfold tlt in *;
    repeat step || t_invert_star || t_star_smallstep_app_onestep.
Qed.

Ltac t_tlt_a_zero :=
  match goal with
  | H: star small_step (tlt ?a zero) ttrue |- _ =>
    poseNew (Mark 0 "t_tlt_a_zero");
    apply False_ind; apply tlt_a_zero with a
  end.

Lemma tlt_zero_b:
  forall b,
    is_nat_value b ->
    star small_step (tlt zero b) ttrue ->
    1 <= tree_size b.
Proof.
  destruct 1; repeat step || t_tlt_a_zero;
    eauto with omega.
Qed.

Ltac t_invert_star_nat_value :=
  match goal with
  | H1: is_nat_value ?v1,
    H2: star small_step ?v1 ?v2 |- _ =>
    unshelve epose proof (star_smallstep_value v1 v2 H2 _); clear H2
  end.

Lemma open_is_nat_value_wf:
  forall v i j rep,
    is_nat_value v ->
    wf rep 0 ->
    wf (open i v rep) j.
Proof.
  induction 1; steps.
Qed.

Hint Resolve open_is_nat_value_wf: bwf.

Lemma tlt_sound:
  forall a,
    is_nat_value a ->
    forall b, is_nat_value b ->
    star small_step (tlt a b) ttrue ->
    tree_size a < tree_size b.
Proof.
  induction 1; steps; eauto using tlt_zero_b.
  destruct H0; repeat step || t_tlt_a_zero; eauto with b_inv.
  assert (is_value ttrue); steps.
  assert (is_value zero); steps.
  apply le_n_S.
  apply_any; steps; eauto with values.
  unfold tlt in *;
    repeat step || t_invert_star ||
           (rewrite open_none in * by (repeat step; eauto with bwf b_inv)) ||
           t_star_smallstep_app_onestep;
    eauto with values.

  eapply star_many_steps in H24; eauto with smallstep bsteplemmas;
    repeat step || unfold irred || t_invert_step.
  apply star_smallstep_app_l; steps.
  eapply Trans; eauto using SPBetaApp with values;
    repeat step || (rewrite open_none in * by (repeat step; eauto with bwf b_inv)).
Qed.

Ltac t_tlt_sound :=
  match goal with
  | H: star small_step (tlt ?a ?b) ttrue |- _ =>
    poseNew (Mark (a,b) "tlt_sound");
    unshelve epose proof (tlt_sound a _ b _ H)
  | H: equivalent (tlt ?a ?b) ttrue |- _ =>
    poseNew (Mark (a,b) "tlt_sound");
    unshelve epose proof (tlt_sound a _ b _ _)
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
  forall a b l tag, psubstitute (tlt a b) l tag = tlt (psubstitute a l tag) (psubstitute b l tag).
Proof.
  unfold tlt; repeat step.
Qed.

Ltac one_step_aux :=
 eapply Trans; [ eauto using is_nat_value_build_nat with values smallstep bsteplemmas | idtac ];
   repeat step || (rewrite open_none in * by (repeat step; eauto using is_nat_value_build_nat with bwf)).

Ltac one_step := unshelve one_step_aux; steps.

Lemma tlt_complete:
  forall a b,
    a < b ->
    star small_step (tlt (build_nat a) (build_nat b)) ttrue.
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
    star small_step (tlt a b) ttrue.
Proof.
  repeat step || t_is_nat_value_buildable || apply tlt_complete || rewrite tree_size_build_nat in *.
Qed.

Lemma true_is_irred: irred ttrue.
Proof.
  unfold irred; repeat step || t_nostep.
Qed.

Lemma equivalent_tlt_steps:
  forall t1 t2 v1 v2,
    equivalent (tlt t1 t2) ttrue ->
    star small_step t1 v1 ->
    star small_step t2 v2 ->
    is_nat_value v1 ->
    is_nat_value v2 ->
    equivalent (tlt v1 v2) ttrue.
Proof.
  unfold tlt; intros.
  apply equivalent_star.
  apply equivalent_true in H.
  apply (star_many_steps _ (app
           (notype_rec v1 (notype_lambda (tmatch (lvar 0 term_var) tfalse ttrue))
              (notype_lambda
                 (tmatch (lvar 0 term_var) tfalse (app (app (lvar 2 term_var) uu) (lvar 0 term_var)))))
           t2)) in H; eauto with bsteplemmas; repeat step || unfold irred || t_nostep.
  inversion H; repeat step || t_invert_step || t_nostep || step_inversion is_value.

  - eapply Trans; eauto with smallstep; steps.
    eapply star_many_steps; eauto with bsteplemmas values; eauto using true_is_irred.
  - eapply Trans; eauto with smallstep; steps.
    eapply star_many_steps; eauto with bsteplemmas values; eauto using true_is_irred.
Qed.
