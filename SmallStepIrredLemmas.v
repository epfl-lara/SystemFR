Require Export SystemFR.StarInversions.

Require Import Coq.Strings.String.

(** Lemmas about operational semantics and stuck terms.              **)
(** At the moment, this file is not used in the rest of the proofs . **)


Lemma true_is_irred: irred ttrue.
Proof.
  unfold irred; repeat step || no_step.
Qed.

Lemma star_smallstep_app_inv_irred:
  forall t v,
    star scbv_step t v ->
    irred v ->
    forall t1 t2,
      t = app t1 t2 ->
      exists v1,
        irred v1 /\
        star scbv_step t1 v1 /\
        star scbv_step (app v1 t2) v.
Proof.
  induction 1; unfold irred; repeat step || t_invert_step;
    eauto with star smallstep step_tactic.
Qed.

Lemma star_smallstep_app_inv_irred2:
  forall t v,
    star scbv_step t v ->
    irred v ->
    forall e t2,
      t = app (notype_lambda e) t2 ->
      exists v2,
        irred v2 /\
        star scbv_step t2 v2.
Proof.
  induction 1; unfold irred; repeat step || t_invert_step;
    eauto with star smallstep step_tactic.
Qed.

Lemma star_smallstep_app_inv_irred3:
  forall t v,
    star scbv_step t v ->
    irred v ->
    forall e t2 v2,
      t = app (notype_lambda e) t2 ->
      star scbv_step t2 v2 ->
      cbv_value v2 ->
      star scbv_step (open 0 e v2) v.
Proof.
  induction 1; unfold irred; repeat step || t_invert_star.
  - inversion H1; steps; eauto with smallstep values exfalso.
  - eapply_any; repeat step.
    inversion H3; repeat step || deterministic_step || no_step.
Qed.

Lemma star_smallstep_pp_inv_irred:
  forall t v,
    star scbv_step t v ->
    irred v ->
    forall t1 t2,
      t = pp t1 t2 ->
      exists v1,
        irred v1 /\
        star scbv_step t1 v1.
Proof.
  induction 1; unfold irred; repeat step || t_invert_step; eauto with smallstep star step_tactic.
Qed.

Lemma star_smallstep_pp_inv_irred2:
  forall t v,
    star scbv_step t v ->
    irred v ->
    forall t1 t2 v1,
      t = pp t1 t2 ->
      star scbv_step t1 v1 ->
      cbv_value v1 ->
      exists v2,
        irred v2 /\
        star scbv_step t2 v2.
Proof.
  induction 1; repeat step || t_invert_step || unfold irred in *.
  - inversion H1; steps; eauto with star smallstep.
  - eapply_any; eauto; steps. inversion H3; repeat step || no_step || deterministic_step.
  - pose proof (H5 _ _ _ eq_refl H3); steps.
    eauto with star.
Qed.

Lemma star_smallstep_pp_inv_irred3:
  forall t v,
    star scbv_step t v ->
    irred v ->
    forall t1 t2 v1 v2,
      t = pp t1 t2 ->
      star scbv_step t1 v1 ->
      star scbv_step t2 v2 ->
      cbv_value v1 ->
      cbv_value v2 ->
      v = pp v1 v2.
Proof.
  induction 1; repeat step || t_invert_step || unfold irred in *.
  - inversion H1; steps; inversion H2; steps; eauto with smallstep exfalso.
  - eapply_any; eauto; steps. inversion H3; repeat step || no_step || deterministic_step.
  - eapply_any; eauto; steps. inversion H4; repeat step || no_step || deterministic_step.
Qed.

Lemma star_smallstep_pi1_inv_irred:
  forall t v,
    star scbv_step t v ->
    irred v ->
    forall t',
      t = pi1 t' ->
      exists v',
        star scbv_step t' v' /\
        irred v'.
Proof.
  induction 1; repeat step || t_invert_step || unfold irred in *;
    eauto 5 with star smallstep.
  exists (pp t2 v2); repeat step || t_invert_step || no_step.
Qed.

Lemma star_smallstep_pi1_inv_irred2:
  forall t v,
    star scbv_step t v ->
    irred v ->
    forall t' a b,
      t = pi1 t' ->
      cbv_value a ->
      cbv_value b ->
      star scbv_step t' (pp a b) ->
      v = a.
Proof.
  induction 1; repeat step || t_invert_step || unfold irred in *.
  - inversion H3; steps; eauto 4 with exfalso smallstep.
  - inversion H5; repeat step || t_invert_star || no_step; eauto with values.
  - eapply_any; eauto; steps. inversion H5; repeat step || deterministic_step || no_step.
Qed.

Lemma star_smallstep_pi2_inv_irred:
  forall t v,
    star scbv_step t v ->
    irred v ->
    forall t',
      t = pi2 t' ->
      exists v',
        star scbv_step t' v' /\
        irred v'.
Proof.
  induction 1; repeat step || t_invert_step || unfold irred in *;
    eauto 5 with star smallstep.
  exists (pp v1 t2); repeat step || t_invert_step || no_step.
Qed.

Lemma star_smallstep_pi2_inv_irred2:
  forall t v,
    star scbv_step t v ->
    irred v ->
    forall t' a b,
      t = pi2 t' ->
      cbv_value a ->
      cbv_value b ->
      star scbv_step t' (pp a b) ->
      v = b.
Proof.
  induction 1; repeat step || t_invert_step || unfold irred in *.
  - inversion H3; steps; eauto 4 with exfalso smallstep.
  - inversion H5; repeat step || t_invert_star || no_step; eauto with values.
  - apply H6 with t0 a; steps. inversion H5; repeat step || deterministic_step || no_step.
Qed.

Lemma star_smallstep_succ_inv_irred:
  forall t v,
    star scbv_step t v ->
    irred v ->
    forall t',
      t = succ t' ->
      exists v',
        star scbv_step t' v' /\
        v = succ v' /\
        irred v'.
Proof.
  induction 1; repeat step || t_invert_step || unfold irred in *;
    eauto 6 with star smallstep.
Qed.

Lemma star_smallstep_ite_inv_irred:
  forall t v,
    star scbv_step t v ->
    irred v ->
    forall t1 t2 t3,
      t = ite t1 t2 t3 ->
      exists v1,
        irred v1 /\
        star scbv_step t1 v1 /\
        star scbv_step (ite v1 t2 t3) v.
Proof.
  induction 1; unfold irred; repeat step.
  - exists t1; steps; eauto with smallstep.
  - inversion H; repeat step.
    + exists ttrue; repeat step || no_step || step_inversion scbv_step; eauto with star smallstep.
    + exists tfalse; repeat step || no_step || step_inversion scbv_step; eauto with star smallstep.
    + exists v1; steps; repeat step; eauto with star smallstep.
Qed.

Lemma star_smallstep_ite_true_irred:
  forall t v,
    star scbv_step t v ->
    irred v ->
    forall t2 t3,
      t = ite ttrue t2 t3 ->
      star scbv_step t2 v.
Proof.
  induction 1; unfold irred; repeat step || t_invert_step; eauto with exfalso smallstep.
Qed.

Lemma star_smallstep_ite_false_irred:
  forall t v,
    star scbv_step t v ->
    irred v ->
    forall t2 t3,
      t = ite tfalse t2 t3 ->
      star scbv_step t3 v.
Proof.
  induction 1; unfold irred; repeat step || t_invert_step; eauto with exfalso smallstep.
Qed.

Lemma star_smallstep_match_inv_irred:
  forall t v,
    star scbv_step t v ->
    irred v ->
    forall t1 t2 t3,
      t = tmatch t1 t2 t3 ->
      exists v1,
        irred v1 /\
        star scbv_step t1 v1 /\
        star scbv_step (tmatch v1 t2 t3) v.
Proof.
  induction 1; unfold irred; repeat step.
  - exists t1; steps; eauto with smallstep.
  - inversion H; repeat step.
    + exists zero; repeat step || no_step; eauto with star smallstep.
    + exists (succ v); steps; repeat step || t_invert_step || no_step; eauto with star smallstep.
    + exists v1; steps; repeat step; eauto with star smallstep.
Qed.

Lemma star_smallstep_irred:
  forall t t1,
    star scbv_step t t1 ->
    forall t2,
      star scbv_step t t2 ->
      irred t1 ->
      irred t2 ->
      t1 = t2.
Proof.
  induction 1; unfold irred; steps; eauto.
  - inversion H; repeat step; eauto with exfalso.
  - inversion H1; repeat step || deterministic_step; eauto with exfalso.
Qed.

Ltac t_deterministic_star_irred :=
    match goal with
    | H1: star scbv_step ?t ?v1,
      H2: star scbv_step ?t ?v2 |- _ =>
      poseNew (Mark (v1,v2) "equality");
      unshelve epose proof (star_smallstep_irred _ _ H1 _ H2 _ _)
    end; eauto with values.

Lemma star_smallstep_irred2:
  forall t t1,
    star scbv_step t t1 ->
    forall v,
      star scbv_step t v ->
      irred t1 ->
      cbv_value v ->
      t1 = v.
Proof.
  eauto using value_irred, star_smallstep_irred.
Qed.

Ltac hyp_irred v :=
  match goal with
  | H: irred v |- _ => idtac
  end.
Ltac t_not_hyp_irred t := tryif hyp_irred t then fail else idtac.

Ltac t_invert_irred :=
  match goal with
  | H1: star scbv_step ?t ?t1,
    H2: star scbv_step ?t ?t2,
    H3: irred ?t1,
    H4: irred ?t2 |- _ =>
    poseNew (Mark (t1,t2) "equality");
    pose proof (star_smallstep_irred _ _ H1 _ H2 H3 H4)
  | H1: star scbv_step ?t ?t1,
    H2: star scbv_step ?t ?t2,
    H3: irred ?t1,
    H4: cbv_value ?t2 |- _ =>
    poseNew (Mark (t1,t2) "equality");
    pose proof (star_smallstep_irred2 _ _ H1 _ H2 H3 H4)
  | H1: irred ?v,
    H2: star scbv_step (ite ?t1 ?t2 ?t3) ?v |- _ =>
    (t_not_hyp_irred t1);
    poseNew (Mark H2 "inv ite");
    pose proof (star_smallstep_ite_inv_irred _ v H2 H1 t1 t2 t3 eq_refl)
  | H1: irred ?v,
    H2: star scbv_step (ite ttrue ?t2 ?t3) ?v |- _ =>
    poseNew (Mark H2 "inv ite true");
    pose proof (star_smallstep_ite_true_irred _ v H2 H1 t2 t3 eq_refl)
  | H1: irred ?v,
    H2: star scbv_step (ite tfalse ?t2 ?t3) ?v |- _ =>
    poseNew (Mark H2 "inv ite false");
    pose proof (star_smallstep_ite_false_irred _ v H2 H1 t2 t3 eq_refl)

 | H1: irred ?v,
    H2: star scbv_step (app ?t1 ?t2) ?v |- _ =>
    (t_not_hyp_irred t1);
    poseNew (Mark H2 "inv app");
    pose proof (star_smallstep_app_inv_irred _ v H2 H1 t1 t2 eq_refl)

 | H1: irred ?v,
    H2: star scbv_step (tmatch ?t1 ?t2 ?t3) ?v |- _ =>
    (t_not_hyp_irred t1);
    poseNew (Mark H2 "inv match");
    pose proof (star_smallstep_match_inv_irred _ v H2 H1 t1 t2 t3 eq_refl)

 | H1: irred ?v,
    H2: star scbv_step (pi1 ?t1) ?v |- _ =>
    (t_not_hyp_irred t1);
    poseNew (Mark H2 "inv pi1");
    pose proof (star_smallstep_pi1_inv_irred _ v H2 H1 t1 eq_refl)

 | H1: irred ?v,
    H2: star scbv_step (pi1 ?t1) ?v,
    H3: star scbv_step ?t1 (pp ?a ?b),
    H4: cbv_value ?a,
    H5: cbv_value ?b
    |- _ =>
    (t_not_hyp_irred t1);
    poseNew (Mark H2 "inv2 pi1");
    pose proof (star_smallstep_pi1_inv_irred2 _ v H2 H1 t1 a b eq_refl H4 H5 H3)
  | H1: irred ?v,
    H2: star scbv_step (pi2 ?t1) ?v |- _ =>
    (t_not_hyp_irred t1);
    poseNew (Mark H2 "inv pi2");
    unshelve epose proof (star_smallstep_pi2_inv_irred _ v H2 H1 t1 eq_refl)
  | H1: irred ?v,
    H2: star scbv_step (pi2 ?t1) ?v,
    H3: star scbv_step ?t1 (pp ?a ?b),
    H4: cbv_value ?a,
    H5: cbv_value ?b
    |- _ =>
    (t_not_hyp_irred t1);
    poseNew (Mark H2 "inv2 pi2");
    pose proof (star_smallstep_pi2_inv_irred2 _ v H2 H1 t1 a b eq_refl H4 H5 H3)
  | H1: irred ?v,
    H2: star scbv_step (succ ?t1) ?v |- _ =>
    (t_not_hyp_irred t1);
    poseNew (Mark H2 "inv succ");
    unshelve epose proof (star_smallstep_succ_inv_irred _ v H2 H1 t1 eq_refl)
  | H1: irred ?v,
    H2: star scbv_step (pp ?t1 ?t2) ?v |- _ =>
    (t_not_hyp_irred t1);
    poseNew (Mark H2 "inv pp");
    unshelve epose proof (star_smallstep_pp_inv_irred _ v H2 H1 t1 t2 eq_refl)
  | H1: irred ?v,
    H2: star scbv_step (pp ?t1 ?t2) ?v,
    H3: star scbv_step ?t1 ?v1,
    H4: cbv_value ?v1
    |- _ =>
    (t_not_hyp_irred t1);
    poseNew (Mark H2 "inv2 pp");
    pose proof (star_smallstep_pp_inv_irred2 _ v H2 H1 t1 t2 v1 eq_refl H3 H4)
  | H1: irred ?v,
    H2: star scbv_step (pp ?t1 ?t2) ?v,
    H3: star scbv_step ?t1 ?v1,
    H4: star scbv_step ?t2 ?v2,
    H5: cbv_value ?v1,
    H6: cbv_value ?v2
    |- _ =>
    (t_not_hyp_irred t1);
    poseNew (Mark H2 "inv3 pp");
    pose proof (star_smallstep_pp_inv_irred3 _ v H2 H1 t1 t2 v1 v2 eq_refl H3 H4 H5 H6)
  end.
