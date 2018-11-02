Require Import Termination.Tactics.
Require Import Termination.TermProperties.
Require Import Termination.Syntax.
Require Import Termination.SmallStep.
Require Import Termination.ListUtils.
Require Import Termination.StarLemmas.
Require Import Termination.StarInversions.

Lemma star_smallstep_let_inv_irred:
  forall t v,
    star small_step t v ->
    irred v ->
    forall t1 T t2,
      t = tlet t1 T t2 ->
      exists v1,
        irred v1 /\
        star small_step t1 v1 /\
        star small_step (tlet v1 T t2) v.
Proof.
  induction 1; unfold irred; repeat step.
  - exists t1; steps; eauto with smallstep.
  - inversion H; repeat step.
    + exists t0; steps; repeat step || unshelve eauto with smallstep.
    + exists v1; steps; repeat step; eauto with smallstep.
Qed.

Lemma star_smallstep_let_inv_irred2:
  forall t v,
    star small_step t v ->
    irred v ->
    forall w T e,
      t = tlet w T e ->
      is_value w ->
      star small_step (open 0 e w) v.
Proof.
  induction 1; unfold irred; repeat step || t_invert_star;
    eauto 4 with falsity smallstep.
Qed.


Lemma star_smallstep_app_inv_irred:
  forall t v,
    star small_step t v ->
    irred v ->
    forall t1 t2,
      t = app t1 t2 ->
      exists v1,
        irred v1 /\
        star small_step t1 v1 /\
        star small_step (app v1 t2) v.
Proof.
  induction 1; unfold irred; repeat step.
  - exists t1; steps; eauto with smallstep.
  - inversion H; repeat step.
    + exists (lambda T t); repeat step || unshelve eauto with smallstep.
    + exists v1; steps; repeat step || unshelve eauto with smallstep.
    + exists t0; steps; repeat step || unshelve eauto with smallstep.
Qed.

Lemma star_smallstep_app_inv_irred2:
  forall t v,
    star small_step t v ->
    irred v ->
    forall T e t2,
      t = app (lambda T e) t2 ->
      exists v2,
        irred v2 /\
        star small_step t2 v2.
Proof.
  induction 1; unfold irred; repeat step.
  - exists t2; steps; eauto with smallstep values.
  - inversion H; repeat step || unshelve eauto 3 with smallstep;
      eauto with step_tactic smallstep.
Qed.

Lemma star_smallstep_app_inv_irred3:
  forall t v,
    star small_step t v ->
    irred v ->
    forall T e t2 v2,
      t = app (lambda T e) t2 ->
      star small_step t2 v2 ->
      is_value v2 ->
      star small_step (open 0 e v2) v.
Proof.
  induction 1; unfold irred; repeat step || t_invert_star.
  - inversion H1; steps.
    + apply False_ind; eapply H; eauto with smallstep.
    + apply False_ind; eapply H; eauto with smallstep values.
  - eapply H5; repeat step.
    inversion H3; repeat step || t_deterministic_step || t_nostep.
Qed.

Lemma star_smallstep_pp_inv_irred:
  forall t v,
    star small_step t v ->
    irred v ->
    forall t1 t2,
      t = pp t1 t2 ->
      exists v1,
        irred v1 /\
        star small_step t1 v1.
Proof.
  induction 1; unfold irred; repeat step || t_invert_step; eauto with smallstep step_tactic. 
Qed.

Lemma star_smallstep_pp_inv_irred2:
  forall t v,
    star small_step t v ->
    irred v ->
    forall t1 t2 v1,
      t = pp t1 t2 ->
      star small_step t1 v1 ->
      is_value v1 ->
      exists v2,
        irred v2 /\
        star small_step t2 v2.
Proof.
  induction 1; repeat step || t_invert_step || unfold irred in *.
  - inversion H1; steps; eauto with smallstep.
  - eapply_any; eauto; steps. inversion H3; repeat step || t_nostep || t_deterministic_step.
  - pose proof (H5 _ _ _ eq_refl H3); steps.
    eauto with smallstep.
Qed.

Lemma star_smallstep_pp_inv_irred3:
  forall t v,
    star small_step t v ->
    irred v ->
    forall t1 t2 v1 v2,
      t = pp t1 t2 ->
      star small_step t1 v1 ->
      star small_step t2 v2 ->
      is_value v1 ->
      is_value v2 ->
      v = pp v1 v2.
Proof.
  induction 1; repeat step || t_invert_step || unfold irred in *.
  - inversion H1; steps; inversion H2; steps; eauto with smallstep falsity.
  - eapply_any; eauto; steps. inversion H3; repeat step || t_nostep || t_deterministic_step.
  - eapply_any; eauto; steps. inversion H4; repeat step || t_nostep || t_deterministic_step.
Qed.

Lemma star_smallstep_pi1_inv_irred:
  forall t v,
    star small_step t v ->
    irred v ->
    forall t',
      t = pi1 t' ->
      exists v',
        star small_step t' v' /\
        irred v'.
Proof.
  induction 1; repeat step || t_invert_step || unfold irred in *.
  - eauto 5 with smallstep.
  - exists (pp t2 v2); repeat step || t_invert_step || t_nostep.
  - eauto 4 with smallstep.
Qed.

Lemma star_smallstep_pi1_inv_irred2:
  forall t v,
    star small_step t v ->
    irred v ->
    forall t' a b,
      t = pi1 t' ->
      is_value a ->
      is_value b ->
      star small_step t' (pp a b) ->
      v = a.
Proof.
  induction 1; repeat step || t_invert_step || unfold irred in *.
  - inversion H3; steps; eauto 4 with falsity smallstep.
  - inversion H5; repeat step || t_invert_star || t_nostep.
  - eapply_any; eauto; steps. inversion H5; repeat step || t_deterministic_step || t_nostep.
Qed.

Lemma star_smallstep_pi2_inv_irred:
  forall t v,
    star small_step t v ->
    irred v ->
    forall t',
      t = pi2 t' ->
      exists v',
        star small_step t' v' /\
        irred v'.
Proof.
  induction 1; repeat step || t_invert_step || unfold irred in *.
  - eauto 5 with smallstep.
  - exists (pp v1 t2); repeat step || t_invert_step || t_nostep.
  - eauto 4 with smallstep.
Qed.

Lemma star_smallstep_pi2_inv_irred2:
  forall t v,
    star small_step t v ->
    irred v ->
    forall t' a b,
      t = pi2 t' ->
      is_value a ->
      is_value b ->
      star small_step t' (pp a b) ->
      v = b.
Proof.
  induction 1; repeat step || t_invert_step || unfold irred in *.
  - inversion H3; steps; eauto 4 with falsity smallstep.
  - inversion H5; repeat step || t_invert_star || t_nostep.
  - apply H6 with t0 a; steps. inversion H5; repeat step || t_deterministic_step || t_nostep.
Qed.

Lemma star_smallstep_succ_inv_irred:
  forall t v,
    star small_step t v ->
    irred v ->
    forall t',
      t = succ t' ->
      exists v',
        star small_step t' v' /\
        v = succ v' /\
        irred v'.
Proof.
  induction 1; repeat step || t_invert_step || unfold irred in *; eauto 6 with smallstep.
Qed.

Lemma star_smallstep_ite_inv_irred:
  forall t v,
    star small_step t v ->
    irred v ->
    forall t1 t2 t3,
      t = ite t1 t2 t3 ->
      exists v1,
        irred v1 /\
        star small_step t1 v1 /\
        star small_step (ite v1 t2 t3) v.
Proof.
  induction 1; unfold irred; repeat step.
  - exists t1; steps; eauto with smallstep.
  - inversion H; repeat step.
    + exists ttrue; repeat step || t_nostep || step_inversion small_step; eauto with smallstep.
    + exists tfalse; repeat step || t_nostep || step_inversion small_step; eauto with smallstep.
    + exists v1; steps; repeat step; eauto with smallstep.
Qed.

Lemma star_smallstep_ite_true_irred:
  forall t v,
    star small_step t v ->
    irred v ->
    forall t2 t3,
      t = ite ttrue t2 t3 ->
      star small_step t2 v.
Proof.
  induction 1; unfold irred; repeat step || t_invert_step; eauto with falsity smallstep.
Qed.    

Lemma star_smallstep_ite_false_irred:
  forall t v,
    star small_step t v ->
    irred v ->
    forall t2 t3,
      t = ite tfalse t2 t3 ->
      star small_step t3 v.
Proof.
  induction 1; unfold irred; repeat step || t_invert_step; eauto with falsity smallstep.
Qed.    

Lemma star_smallstep_rec_inv_irred:
  forall t v,
    star small_step t v ->
    irred v ->
    forall T t1 t2 t3,
      t = rec T t1 t2 t3 ->
      exists v1,
        irred v1 /\
        star small_step t1 v1 /\
        star small_step (rec T v1 t2 t3) v.
Proof.
  induction 1; unfold irred; repeat step.
  - exists t1; steps; eauto with smallstep.
  - inversion H; repeat step.
    + exists zero; repeat step; eauto with smallstep.
    + exists (succ v); steps; repeat step; eauto with smallstep.
    + exists v1; steps; repeat step; eauto with smallstep.
Qed.

Lemma star_smallstep_match_inv_irred:
  forall t v,
    star small_step t v ->
    irred v ->
    forall t1 t2 t3,
      t = tmatch t1 t2 t3 ->
      exists v1,
        irred v1 /\
        star small_step t1 v1 /\
        star small_step (tmatch v1 t2 t3) v.
Proof.
  induction 1; unfold irred; repeat step.
  - exists t1; steps; eauto with smallstep.
  - inversion H; repeat step.
    + exists zero; repeat step; eauto with smallstep.
    + exists (succ v); steps; repeat step; eauto with smallstep.
    + exists v1; steps; repeat step; eauto with smallstep.
Qed.

Lemma star_smallstep_irred:
  forall t t1,
    star small_step t t1 ->
    forall t2,
      star small_step t t2 ->
      irred t1 ->
      irred t2 ->
      t1 = t2.
Proof.
  induction 1; unfold irred; steps; eauto.
  - inversion H; repeat step; eauto with falsity.
  - inversion H1; repeat step || t_deterministic_step; eauto with falsity.
Qed.

Lemma star_smallstep_irred2:
  forall t t1,
    star small_step t t1 ->
    forall v,
      star small_step t v ->
      irred t1 ->
      is_value v ->
      t1 = v.
Proof.
  eauto using value_irred, star_smallstep_irred.
Qed.
  

Ltac t_invert_irred :=
  match goal with
  | H1: star small_step ?t ?t1,
    H2: star small_step ?t ?t2,
    H3: irred ?t1,
    H4: irred ?t2 |- _ =>
    poseNew (Mark (t1,t2) "equality");
    pose proof (star_smallstep_irred _ _ H1 _ H2 H3 H4)
  | H1: star small_step ?t ?t1,
    H2: star small_step ?t ?t2,
    H3: irred ?t1,
    H4: is_value ?t2 |- _ => 
    poseNew (Mark (t1,t2) "equality");
    pose proof (star_smallstep_irred2 _ _ H1 _ H2 H3 H4)
  | H1: irred ?v,
    H2: star small_step (ite ?t1 ?t2 ?t3) ?v |- _ =>
    (t_not_hyp_irred t1);
    poseNew (Mark H2 "inv ite");
    pose proof (star_smallstep_ite_inv_irred _ v H2 H1 t1 t2 t3 eq_refl)
  | H1: irred ?v,
    H2: star small_step (ite ttrue ?t2 ?t3) ?v |- _ =>
    poseNew (Mark H2 "inv ite true");
    pose proof (star_smallstep_ite_true_irred _ v H2 H1 t2 t3 eq_refl)
  | H1: irred ?v,
    H2: star small_step (ite tfalse ?t2 ?t3) ?v |- _ =>
    poseNew (Mark H2 "inv ite false");
    pose proof (star_smallstep_ite_false_irred _ v H2 H1 t2 t3 eq_refl)

 | H1: irred ?v,
    H2: star small_step (app ?t1 ?t2) ?v |- _ =>
    (t_not_hyp_irred t1);
    poseNew (Mark H2 "inv app");
    pose proof (star_smallstep_app_inv_irred _ v H2 H1 t1 t2 eq_refl)

 | H1: irred ?v,
    H2: star small_step (tlet ?t1 ?T ?t2) ?v |- _ =>
    poseNew (Mark H2 "inv tlet");
    pose proof (star_smallstep_let_inv_irred _ v H2 H1 t1 T t2 eq_refl)

 | H1: irred ?v,
    H2: star small_step (rec ?T ?t1 ?t2 ?t3) ?v |- _ =>
    (t_not_hyp_irred t1);
    poseNew (Mark H2 "inv rec");
    pose proof (star_smallstep_rec_inv_irred _ v H2 H1 T t1 t2 t3 eq_refl)

 | H1: irred ?v,
    H2: star small_step (tmatch ?t1 ?t2 ?t3) ?v |- _ =>
    (t_not_hyp_irred t1);
    poseNew (Mark H2 "inv match");
    pose proof (star_smallstep_match_inv_irred _ v H2 H1 t1 t2 t3 eq_refl)

 | H1: irred ?v,
    H2: star small_step (pi1 ?t1) ?v |- _ =>
    (t_not_hyp_irred t1);
    poseNew (Mark H2 "inv pi1");
    pose proof (star_smallstep_pi1_inv_irred _ v H2 H1 t1 eq_refl)

 | H1: irred ?v,
    H2: star small_step (pi1 ?t1) ?v,
    H3: star small_step ?t1 (pp ?a ?b),
    H4: is_value ?a,
    H5: is_value ?b
    |- _ =>
    (t_not_hyp_irred t1);
    poseNew (Mark H2 "inv2 pi1");
    pose proof (star_smallstep_pi1_inv_irred2 _ v H2 H1 t1 a b eq_refl H4 H5 H3)
  | H1: irred ?v,
    H2: star small_step (pi2 ?t1) ?v |- _ =>
    (t_not_hyp_irred t1);
    poseNew (Mark H2 "inv pi2");
    unshelve epose proof (star_smallstep_pi2_inv_irred _ v H2 H1 t1 eq_refl)
  | H1: irred ?v,
    H2: star small_step (pi2 ?t1) ?v,
    H3: star small_step ?t1 (pp ?a ?b),
    H4: is_value ?a,
    H5: is_value ?b
    |- _ =>
    (t_not_hyp_irred t1);
    poseNew (Mark H2 "inv2 pi2");
    pose proof (star_smallstep_pi2_inv_irred2 _ v H2 H1 t1 a b eq_refl H4 H5 H3)
  | H1: irred ?v,
    H2: star small_step (succ ?t1) ?v |- _ =>
    (t_not_hyp_irred t1);
    poseNew (Mark H2 "inv succ");
    unshelve epose proof (star_smallstep_succ_inv_irred _ v H2 H1 t1 eq_refl)
  | H1: irred ?v,
    H2: star small_step (pp ?t1 ?t2) ?v |- _ =>
    (t_not_hyp_irred t1);
    poseNew (Mark H2 "inv pp");
    unshelve epose proof (star_smallstep_pp_inv_irred _ v H2 H1 t1 t2 eq_refl)
  | H1: irred ?v,
    H2: star small_step (pp ?t1 ?t2) ?v,
    H3: star small_step ?t1 ?v1,
    H4: is_value ?v1
    |- _ =>
    (t_not_hyp_irred t1);
    poseNew (Mark H2 "inv2 pp");
    pose proof (star_smallstep_pp_inv_irred2 _ v H2 H1 t1 t2 v1 eq_refl H3 H4)
  | H1: irred ?v,
    H2: star small_step (pp ?t1 ?t2) ?v,
    H3: star small_step ?t1 ?v1,
    H4: star small_step ?t2 ?v2,
    H5: is_value ?v1,
    H6: is_value ?v2
    |- _ =>
    (t_not_hyp_irred t1);
    poseNew (Mark H2 "inv3 pp");
    pose proof (star_smallstep_pp_inv_irred3 _ v H2 H1 t1 t2 v1 v2 eq_refl H3 H4 H5 H6)
  end.
