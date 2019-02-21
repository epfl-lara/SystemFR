Require Import Termination.Trees.
Require Import Termination.Syntax.
Require Import Termination.StarInversions.
Require Import Termination.StarRelation.
Require Import Termination.StarLemmas.
Require Import Termination.SmallStep.
Require Import Termination.Tactics.
Require Import Termination.WFLemmas.
Require Import Termination.WellFormed.
Require Import Termination.WFLemmasEval.
Require Import Termination.TermProperties.
Require Import Termination.TypeErasure.
Require Import Termination.TypeErasureLemmas.

Require Import Coq.Strings.String.

Definition annotated_tlt (a: tree) (b: tree) :=
  app
    (rec (T_arrow T_nat T_nat) a
      (lambda T_nat (tmatch (lvar 0 term_var) tfalse ttrue))
      (lambda T_nat (tmatch (lvar 0 term_var) tfalse (app (app (lvar 2 term_var) uu) (lvar 0 term_var)))))
    b.

Definition tlt (a: tree) (b: tree) :=
  app
    (notype_rec a
      (notype_lambda (tmatch (lvar 0 term_var) tfalse ttrue))
      (notype_lambda (tmatch (lvar 0 term_var) tfalse (app (app (lvar 2 term_var) uu) (lvar 0 term_var)))))
    b.

Lemma tlt_erase:
  forall a b, erase_term (annotated_tlt a b) = tlt (erase_term a) (erase_term b).
Proof.
  unfold tlt, annotated_tlt; steps.
Qed.

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
  unfold tlt in *; destruct a;
    repeat step || t_invert_star || t_star_smallstep_app_onestep.
Qed.

Ltac t_tlt_a_zero :=
  match goal with
  | H: star small_step (tlt ?a zero) ttrue |- _ =>
    apply False_ind; apply tlt_a_zero with a
  end.

Lemma tlt_zero_b:
  forall b,
    is_nat_value b ->
    star small_step (tlt zero b) ttrue ->
    1 <= tree_size b.
Proof.
  destruct b; repeat step || t_tlt_a_zero;
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
  induction v; steps.
Qed.

Hint Resolve open_is_nat_value_wf: bwf.

Lemma tlt_sound:
  forall a b,
    is_nat_value a ->
    is_nat_value b ->
    star small_step (tlt a b) ttrue ->
    tree_size a < tree_size b.
Proof.
  induction a; steps; eauto using tlt_zero_b.
  destruct b; repeat step || t_tlt_a_zero.
  assert (is_value ttrue); steps.
  assert (is_value zero); steps.
  unfold tlt in *;
    repeat step || apply le_n_S || apply_any || t_invert_star ||
           (rewrite open_none in * by (repeat step; eauto with bwf)) ||
           t_star_smallstep_app_onestep;
    eauto with values.

  eapply star_many_steps in H24; eauto with smallstep bsteplemmas; repeat step || unfold irred || t_invert_step.
  apply star_smallstep_app_l; steps.
  eapply Trans; eauto using SPBetaApp with values;
    repeat step || (rewrite open_none in * by (repeat step; eauto with bwf)).
Qed.

Ltac t_tlt_sound :=
  match goal with
  | H: star small_step (tlt ?a ?b) ttrue |- _ =>
    poseNew (Mark (a,b) "tlt_sound");
    unshelve epose proof (tlt_sound a b _ _ H)
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
