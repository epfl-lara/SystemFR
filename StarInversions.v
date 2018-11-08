Require Import Termination.Syntax.
Require Import Termination.SmallStep.
Require Import Termination.TermProperties.
Require Import Termination.Tactics.
Require Import Termination.WFLemmas.
Require Import Termination.ListUtils.
Require Import Termination.StarLemmas.
Require Import Termination.StarRelation.

Lemma star_one_step:
  forall t1 t2 v,
    star small_step t1 v ->
    small_step t1 t2 ->
    irred v ->
    star small_step t2 v.
Proof.
  unfold irred; destruct 1; repeat step || t_deterministic_step; eauto with falsity.
Qed.

Lemma star_many_steps:
  forall t1 t2,
    star small_step t1 t2 ->
    forall v,
      star small_step t1 v ->
      irred v ->
      star small_step t2 v.
Proof.
  unfold irred; induction 1; repeat step || apply_any;
    eauto using star_one_step.
Qed.

Lemma star_smallstep_pi1_val:
  forall t v,
    star small_step t v ->
    forall v1 v2,
      v = pp v1 v2 ->
      is_value v1 ->
      is_value v2 ->
      star small_step (pi1 t) v1.
Proof.
  induction 1; steps; eauto with smallstep.
Qed.

Lemma star_smallstep_pi2_val:
  forall t v,
    star small_step t v ->
    forall v1 v2,
      v = pp v1 v2 ->
      is_value v1 ->
      is_value v2 ->
      star small_step (pi2 t) v2.
Proof.
  induction 1; steps; eauto with smallstep.
Qed.

Lemma normalizing_pair:
  forall t1 t2,
    normalizing t1 ->
    normalizing t2 ->
    normalizing (pp t1 t2).
Proof.
  unfold normalizing;
    repeat match goal with
           | _ => step
           | H: _ = nil |- _ => rewrite H in *
           end; eauto with bsteplemmas values.
Qed.

Lemma star_smallstep_app_inv:
  forall t v,
    star small_step t v ->
    is_value v ->
    forall t1 t2,
      t = app t1 t2 ->
      exists v1 v2,
        is_value v1 /\
        is_value v2 /\
        star small_step t1 v1 /\
        star small_step t2 v2 /\
        star small_step (app v1 v2) v.
Proof.
  induction 1; repeat step || step_inversion is_value; eauto with smallstep.
  inversion H; repeat step || t_listutils; eauto 3 with bsteplemmas smallstep values.
  - exists (notype_lambda t), t4; repeat step;
      eauto 4 with smallstep bsteplemmas values bwf.
  - exists v1, v2; steps; eauto with smallstep.
  - exists v1, v2; steps; eauto with smallstep.
Qed.

Lemma star_smallstep_pp_inv:
  forall t v,
    star small_step t v ->
    is_value v ->
    forall t1 t2,
      t = pp t1 t2 ->
      exists v1 v2,
        is_value v1 /\
        is_value v2 /\
        star small_step t1 v1 /\
        star small_step t2 v2 /\
        v = pp v1 v2.
Proof.
  induction 1; repeat step || step_inversion is_value || t_invert_step;
    eauto 1 with bsteplemmas smallstep;
    eauto 6 with step_tactic smallstep.
Qed.

Lemma star_smallstep_pi1_inv:
  forall t v,
    star small_step t v ->
    is_value v ->
    forall t',
      t = pi1 t' ->
      exists v2,
        is_value v2 /\
        is_value (pp v v2) /\
        star small_step t' (pp v v2).
Proof.
  induction 1; repeat step || step_inversion is_value || t_invert_step; eauto with bsteplemmas.
  - exists v2; steps; eauto with values smallstep bsteplemmas bwf.
  - exists v2; eauto with values smallstep.
Qed.

Lemma star_smallstep_pi2_inv:
  forall t v,
    star small_step t v ->
    is_value v ->
    forall t',
      t = pi2 t' ->
      exists v1,
        is_value v1 /\
        is_value (pp v1 v) /\
        star small_step t' (pp v1 v).
Proof.
  induction 1; repeat step || step_inversion is_value || t_invert_step; eauto with bsteplemmas.
  - exists v1; steps; eauto with values smallstep bsteplemmas.
  - exists v1; steps; eauto with values smallstep.
Qed.

Lemma star_smallstep_ite_inv:
  forall t v,
    star small_step t v ->
    is_value v ->
    forall t1 t2 t3,
      t = ite t1 t2 t3 ->
        (star small_step t1 ttrue /\ star small_step t2 v) \/
        (star small_step t1 tfalse /\ star small_step t3 v).
Proof.
  induction 1; repeat step || step_inversion is_value || t_invert_step;
    eauto with smallstep bsteplemmas bwf.
Qed.

Lemma star_smallstep_succ_inv:
  forall t v,
    star small_step t v ->
    is_value v ->
    forall t',
      t = succ t' ->
      exists v',
        v = succ v' /\
        is_value v' /\
        is_value (succ v') /\
        star small_step t' v'.
Proof.
  induction 1; repeat step || step_inversion is_value || t_invert_step;
    eauto with smallstep values bsteplemmas.
  - exists t'; steps; eauto with smallstep values bwf.
  - exists v'; steps; eauto with values smallstep.
Qed.

Lemma star_smallstep_rec_inv:
  forall t v,
    star small_step t v ->
    is_value v ->
    forall tn t0 ts,
      t = notype_rec tn t0 ts ->
        (star small_step tn zero /\ star small_step t0 v) \/
        exists v',
          star small_step tn (succ v') /\
          is_value v' /\
          is_value (succ v') /\
          star small_step
            (open 0 (open 1 ts v') (notype_lambda (notype_rec v' t0 ts)))
             v.
Proof.
  induction 1;
    repeat match goal with
           | H: forall a b c d, _ |- _ =>
              unshelve epose proof (H _ _ _ _ eq_refl); clear H
           | _ => step || step_inversion is_value || t_invert_step
           end;
    eauto 1 with bsteplemmas;
    eauto 6 with step_tactic smallstep values bwf.
Qed.

Lemma star_smallstep_rec_inv2:
  forall t v,
    star small_step t v ->
    is_value v ->
    forall T tn t0 ts,
      t = rec T tn t0 ts ->
      exists v',
        star small_step tn v' /\
        star small_step (notype_rec v' t0 ts) v /\
        is_value v'.
Proof.
  induction 1;
    repeat match goal with
           | H: forall a b c d, _ |- _ =>
              unshelve epose proof (H _ _ _ _ eq_refl); clear H
           | |- exists v, star small_step zero v /\ _ => exists zero
           | |- exists v, star small_step (succ ?n) v /\ _ => exists (succ n)
           | _ => step || step_inversion is_value || t_invert_step
           end;
    eauto 1 with bsteplemmas;
    eauto 4 with step_tactic smallstep values bwf.
Qed.

Lemma star_smallstep_rec_zero:
  forall t v,
    star small_step t v ->
    is_value v ->
    forall t0 ts,
      t = notype_rec zero t0 ts ->
      star small_step t0 v.
Proof.
  induction 1;
    repeat match goal with
           | H: forall a b c d, _ |- _ =>
              unshelve epose proof (H _ _ _ _ eq_refl); clear H
           | _ => step || step_inversion is_value || t_invert_step
           end.
Qed.

Lemma star_smallstep_rec_succ:
  forall t v,
    star small_step t v ->
    is_value v ->
    forall v' t0 ts,
      is_value v' ->
      t = notype_rec (succ v') t0 ts ->
      star small_step
           (open 0 (open 1 ts v') (notype_lambda (notype_rec v' t0 ts)))
           v.
Proof.
  induction 1;
    repeat match goal with
           | _ => step || step_inversion is_value || t_invert_step
           end; eauto 2 with smallstep.
Qed.

Hint Resolve normalizing_pair: bsteplemmas.

Lemma smallstep_succ_zero:
  forall t1 t2,
    star small_step t1 t2 ->
    forall v,
      t1 = succ v ->
      t2 = zero ->
      False.
Proof.
  induction 1; repeat step || step_inversion small_step.
Qed.

Lemma star_smallstep_match_zero:
  forall t v,
    star small_step t v ->
    is_value v ->
    forall tn t0 ts,
      t = tmatch tn t0 ts ->
      star small_step tn zero ->
      star small_step t0 v.
Proof.
  induction 1; repeat step || step_inversion is_value || t_invert_step.
  inversion H; repeat step || apply_any;
    eauto 3 using smallstep_succ_zero with falsity;
    eauto using value_irred, star_one_step with values.
Qed.

Lemma star_smallstep_match_succ:
  forall t v v0 tn t0 ts,
    is_value v ->
    is_value v0 ->
    star small_step tn (succ v) ->
    star small_step t v0 ->
    star small_step (open 0 ts v) v0 ->
    star small_step (tmatch tn t0 ts) v0.
Proof.
  intros.
  eapply star_smallstep_trans; eauto.
  eapply star_smallstep_trans; eauto with bsteplemmas; eauto with smallstep.
Qed.

Lemma star_smallstep_match_inv_succ:
  forall v v0 tn t0 ts,
    is_value v ->
    is_value v0 ->
    star small_step tn (succ v) ->
    star small_step (tmatch tn t0 ts) v0 ->
    star small_step (open 0 ts v) v0.
Proof.
  intros.
  eapply star_many_steps;
    eauto;
    eauto 5 using star_smallstep_trans with bsteplemmas smallstep;
    eauto using value_irred.
Qed.

Lemma star_smallstep_rec_zero2:
  forall t v,
    star small_step t v ->
    is_value v ->
    forall tn t0 ts,
      t = notype_rec tn t0 ts ->
      star small_step tn zero ->
      star small_step t0 v.
Proof.
  induction 1; repeat step || step_inversion is_value || t_invert_step || apply_any;
    eauto 3 using smallstep_succ_zero with falsity;
    eauto using value_irred, star_one_step with values.
Qed.

Lemma star_smallstep_rec_succ2:
  forall t v v0 tn t0 ts,
    is_value v ->
    is_value v0 ->
    star small_step tn (succ v) ->
    star small_step t v0 ->
    star small_step (open 0 (open 1 ts v) (notype_lambda (notype_rec v t0 ts))) v0 ->
    star small_step (notype_rec tn t0 ts) v0.
Proof.
  intros.
  eapply star_smallstep_trans; eauto.
  eapply star_smallstep_trans; eauto with bsteplemmas; eauto with smallstep.
Qed.

Lemma star_smallstep_rec_inv_succ2:
  forall v v0 tn t0 ts,
    is_value v ->
    is_value v0 ->
    star small_step tn (succ v) ->
    star small_step (notype_rec tn t0 ts) v0 ->
    star small_step (open 0 (open 1 ts v) (notype_lambda (notype_rec v t0 ts))) v0.
Proof.
  intros.
  eapply star_many_steps;
    eauto;
    eauto 5 using star_smallstep_trans with bsteplemmas smallstep;
    eauto using value_irred.
Qed.

Lemma star_smallstep_value:
  forall v1 v2,
    star small_step v1 v2 ->
    is_value v1 ->
    v1 = v2.
Proof.
  induction 1; steps; eauto with smallstep.
Qed.

Lemma star_smallstep_deterministic:
  forall t v,
    star small_step t v ->
    forall v',
      is_value v ->
      is_value v' ->
      star small_step t v' ->
      v = v'.
Proof.
  induction 1; steps; eauto using star_smallstep_value with smallstep.
  inversion H3; repeat step || t_deterministic_step; eauto with smallstep.
Qed.

Lemma star_smallstep_app_onestep:
  forall t v1 v2,
    star small_step (app (notype_lambda t) v1) v2 ->
    is_value v1 ->
    is_value v2 ->
    star small_step (open 0 t v1) v2.
Proof.
  inversion 1; repeat step || step_inversion is_value small_step.
  inversion H0; steps; eauto with smallstep.
Qed.

Ltac t_deterministic_star :=
    match goal with
    | H1: star small_step ?t ?v1,
      H2: star small_step ?t ?v2 |- _ =>
      poseNew (Mark (v1,v2) "equality");
      unshelve epose proof (star_smallstep_deterministic _ _ H1 _ _ _ H2)
    end; eauto with values.

Ltac t_invert_star :=
  match goal with
  | H1: is_value ?v,
    H2: star small_step (app ?t1 ?t2) ?v |- _ =>
    (t_not_hyp_value t1 || t_not_hyp_value t2);
    poseNew (Mark H2 "inv app");
    unshelve epose proof (star_smallstep_app_inv _ v H2 H1 t1 t2 eq_refl)
  | H1: is_value ?v1,
    H2: star small_step ?v1 ?v2 |- _ =>
    pose proof (star_smallstep_value v1 v2 H2 H1); clear H2
  | H: star small_step trefl ?v |- _ =>
    unshelve epose proof (star_smallstep_value _ v H _); clear H; eauto 2 with values
  | H: star small_step ttrue ?v |- _ =>
    unshelve epose proof (star_smallstep_value _ v H _); clear H; eauto 2 with values
  | H: star small_step tfalse ?v |- _ =>
    unshelve epose proof (star_smallstep_value _ v H _); clear H; eauto 2 with values
  | H: star small_step zero ?v |- _ =>
    unshelve epose proof (star_smallstep_value _ v H _); clear H; eauto 2 with values
  | H: star small_step uu ?v |- _ =>
    unshelve epose proof (star_smallstep_value _ v H _); clear H; eauto 2 with values
  | H1: is_value ?v,
    H2: star small_step (pp ?t1 ?t2) ?v |- _ =>
    (t_not_hyp_value t1 || t_not_hyp_value t2);
    poseNew (Mark H2 "inv pair");
    unshelve epose proof (star_smallstep_pp_inv _ v H2 H1 t1 t2 eq_refl)
  | H1: is_value ?v,
    H2: star small_step (pi1 ?t) ?v |- _ =>
    t_not_hyp_value t;
    poseNew (Mark H2 "inv pi1");
    unshelve epose proof (star_smallstep_pi1_inv _ v H2 H1 t eq_refl)
  | H1: is_value ?v,
    H2: star small_step (pi2 ?t) ?v |- _ =>
    t_not_hyp_value t;
    poseNew (Mark H2 "inv pi2");
    unshelve epose proof (star_smallstep_pi2_inv _ v H2 H1 t eq_refl)
  | H1: is_value ?v,
    H2: star small_step (ite _ _ _) ?v |- _ =>
    poseNew (Mark H2 "inv ite");
    unshelve epose proof (star_smallstep_ite_inv _ v H2 H1 _ _ _ eq_refl)
  | H1: is_value ?v,
    H2: star small_step (succ _) ?v |- _ =>
    poseNew (Mark H2 "inv succ");
    unshelve epose proof (star_smallstep_succ_inv _ v H2 H1 _ eq_refl)
  | H1: is_value ?v1,
    H2: is_value ?v2,
    H3: star small_step (notype_rec (succ ?v2) _ _) ?v1 |- _ =>
    poseNew (Mark H3 "inv rec succ");
    unshelve epose proof (star_smallstep_rec_succ _ _ H3 H1 _ _ _ H2 eq_refl)
  | H1: is_value ?v,
    H2: star small_step (notype_rec zero _ _) ?v |- _ =>
    poseNew (Mark H2 "inv rec zero");
    unshelve epose proof (star_smallstep_rec_zero _ v H2 H1 _ _ eq_refl)
  | H: star small_step (lambda _ _) _ |- _ => inversion H; clear H
  | H: star small_step err _ |- _ => inversion H; clear H
  | _ => t_invert_step
  end.

Lemma false_step:
  star small_step tfalse ttrue -> False.
Proof.
  inversion 1; repeat step || t_invert_step.
Qed.
