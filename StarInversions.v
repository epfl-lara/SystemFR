From Stdlib Require Import String.

Require Export SystemFR.StarLemmas.

Lemma star_one_step:
  forall t1 t2 v,
    t1 ~>* v ->
    t1 ~> t2 ->
    irred v ->
    t2 ~>* v.
Proof.
  unfold irred; destruct 1; repeat step || deterministic_step; eauto with exfalso.
Qed.

Lemma star_one_step2:
  forall t1 t2 t2',
    t1 ~>* t2 ->
    t1 ~> t2' ->
      (t1 = t2 \/ t2' ~>* t2).
Proof.
  inversion 1;
    repeat step || deterministic_step.
Qed.

Lemma star_many_steps:
  forall t1 t2,
    t1 ~>* t2 ->
    forall v,
      t1 ~>* v ->
      irred v ->
      t2 ~>* v.
Proof.
  unfold irred; induction 1; repeat step || apply_any;
    eauto using star_one_step.
Qed.

Lemma star_smallstep_pi1_val:
  forall t v,
    t ~>* v ->
    forall v1 v2,
      v = pp v1 v2 ->
      cbv_value v1 ->
      cbv_value v2 ->
      pi1 t ~>* v1.
Proof.
  induction 1; steps; eauto with smallstep star.
Qed.

Lemma star_smallstep_pi2_val:
  forall t v,
    t ~>* v ->
    forall v1 v2,
      v = pp v1 v2 ->
      cbv_value v1 ->
      cbv_value v2 ->
      pi2 t ~>* v2.
Proof.
  induction 1; steps; eauto with smallstep star.
Qed.

Lemma scbv_normalizing_pair:
  forall t1 t2,
    scbv_normalizing t1 ->
    scbv_normalizing t2 ->
    scbv_normalizing (pp t1 t2).
Proof.
  unfold scbv_normalizing;
    repeat match goal with
           | _ => step
           | H: _ = nil |- _ => rewrite H in *
           end; eauto with cbvlemmas values.
Qed.

Lemma star_smallstep_app_inv:
  forall t v,
    t ~>* v ->
    cbv_value v ->
    forall t1 t2,
      t = app t1 t2 ->
      exists v1 v2,
        cbv_value v1 /\
        cbv_value v2 /\
        t1 ~>* v1 /\
        t2 ~>* v2 /\
        app v1 v2 ~>* v.
Proof.
  induction 1; repeat step || step_inversion cbv_value; eauto with smallstep.
  inversion H; repeat step || list_utils; eauto 3 with cbvlemmas smallstep values.
  - exists (notype_lambda t), t2; repeat step; eauto 4 with smallstep cbvlemmas values star.
  - exists v1, v2; steps; eauto with smallstep star.
  - exists v1, v2; steps; eauto with smallstep star.
Qed.

Lemma star_smallstep_pp_inv:
  forall t v,
    t ~>* v ->
    cbv_value v ->
    forall t1 t2,
      t = pp t1 t2 ->
      exists v1 v2,
        cbv_value v1 /\
        cbv_value v2 /\
        t1 ~>* v1 /\
        t2 ~>* v2 /\
        v = pp v1 v2.
Proof.
  induction 1; repeat step || step_inversion cbv_value || t_invert_step;
    eauto with step_tactic smallstep star.
Qed.

Lemma star_smallstep_pi1_inv:
  forall t v,
    t ~>* v ->
    cbv_value v ->
    forall t',
      t = pi1 t' ->
      exists v2,
        cbv_value v2 /\
        cbv_value (pp v v2) /\
        t' ~>* pp v v2.
Proof.
  induction 1; repeat step || step_inversion cbv_value || t_invert_step; eauto with cbvlemmas.
  - exists v2; steps; eauto with values smallstep cbvlemmas.
  - exists v2; eauto with values smallstep star.
Qed.

Lemma star_smallstep_pi2_inv:
  forall t v,
    t ~>* v ->
    cbv_value v ->
    forall t',
      t = pi2 t' ->
      exists v1,
        cbv_value v1 /\
        cbv_value (pp v1 v) /\
        t' ~>* pp v1 v.
Proof.
  induction 1; repeat step || step_inversion cbv_value || t_invert_step; eauto with cbvlemmas.
  - exists v1; steps; eauto with values smallstep cbvlemmas.
  - exists v1; steps; eauto with values smallstep star.
Qed.

Lemma star_smallstep_unary_primitive_inv:
  forall t v,
    t ~>* v ->
    cbv_value v ->
    forall t' o,
      t = unary_primitive o t' ->
      exists v1,
        cbv_value v1 /\ t' ~>* v1.
Proof.
  induction 1; repeat step || step_inversion cbv_value || t_invert_step; eauto with cbvlemmas.
  exists ttrue; steps.
  exists tfalse; steps.
  exists v1; steps; eauto with values smallstep star cbvlemmas.
Qed.


Lemma star_smallstep_value:
  forall v1 v2,
    v1 ~>* v2 ->
    cbv_value v1 ->
    v1 = v2.
Proof.
  induction 1; repeat step || no_step.
Qed.

Ltac star_smallstep_value :=
  match goal with
  | H: ?v1 ~>* ?v2 |- _ =>
    cbv_value v1;
    unshelve epose proof (star_smallstep_value v1 v2 H _); clear H
  end.

Lemma star_smallstep_build_nat:
  forall n v,
    build_nat n ~>* v ->
    cbv_value v ->
    v = build_nat n.
Proof.
  intros.
  apply star_smallstep_value in H; steps; eauto with values.
Qed.

Ltac star_smallstep_build_nat :=
  match goal with
  |H1: build_nat ?n ~>* ?v, H2: cbv_value ?v |- _ =>
   pose proof (star_smallstep_build_nat n v H1 H2); clear H1; subst
  end.



Opaque PeanoNat.Nat.leb.
Opaque PeanoNat.Nat.ltb.

Lemma star_smallstep_binary_primitive_inv:
  forall t v,
    t ~>* v ->
    cbv_value v ->
    forall t1 t2 o,
      t = binary_primitive o t1 t2 ->
      exists v1 v2,
        cbv_value v1 /\ t1 ~>* v1 /\ cbv_value v2 /\ t2 ~>* v2 /\ binary_primitive o v1 v2 ~> v.
Proof.
  induction 1; repeat steps || step_inversion cbv_value || t_invert_step || star_smallstep_value;
    eauto with cbvlemmas star smallstep values.
    all: try solve [eexists; eexists;
      repeat steps ||
             (match goal with
             | H: ?t ~>* ?v |- ?t ~>* _ => eassumption
             | H1: ?t1 ~> ?t2, H2: ?t2 ~>* ?v |- _ =>
               cbv_value v ; apply (Relation_Operators.rt1n_trans _ _ _ _ _ H1) in H2
             | H: _ |- ?v ~>* ?v' => cbv_value v ; apply Relation_Operators.rt1n_refl
             | H:_ |- binary_primitive _ _ _ ~> _  =>  eapply scbv_step_same; try constructor
              end);
      try solve [ apply cbv_value_build_nat];
      eauto using Relation_Operators.rt1n_refl, Relation_Operators.rt1n_trans with values; steps].
Qed.


Lemma star_smallstep_ite_inv:
  forall t v,
    t ~>* v ->
    cbv_value v ->
    forall t1 t2 t3,
      t = ite t1 t2 t3 ->
        (t1 ~>* ttrue /\ t2 ~>* v) \/
        (t1 ~>* tfalse /\ t3 ~>* v).
Proof.
  induction 1; repeat step || step_inversion cbv_value || t_invert_step;
    eauto with smallstep cbvlemmas star.
Qed.

Lemma star_smallstep_ite_true:
  forall b t1 t2 v,
    b ~>* ttrue ->
    t1 ~>* v ->
    ite b t1 t2 ~>* v.
Proof.
  eauto using star_trans with smallstep cbvlemmas.
Qed.

Lemma star_smallstep_ite_false:
  forall b t1 t2 v,
    b ~>* tfalse ->
    t2 ~>* v ->
    ite b t1 t2 ~>* v.
Proof.
  eauto using star_trans with smallstep cbvlemmas.
Qed.

Lemma star_smallstep_succ_inv:
  forall t v,
    t ~>* v ->
    cbv_value v ->
    forall t',
      t = succ t' ->
      exists v',
        v = succ v' /\
        cbv_value v' /\
        cbv_value (succ v') /\
        t' ~>* v'.
Proof.
  induction 1; repeat step || step_inversion cbv_value || t_invert_step;
    eauto with smallstep values cbvlemmas.
  - exists t'; steps; eauto with smallstep values star.
  - exists v'; steps; eauto with values smallstep star.
Qed.

#[export]
Hint Resolve scbv_normalizing_pair: cbvlemmas.

Lemma smallstep_succ_zero:
  forall t1 t2,
    t1 ~>* t2 ->
    forall v,
      t1 = succ v ->
      t2 = zero ->
      False.
Proof.
  induction 1; repeat step || step_inversion scbv_step.
Qed.

Lemma star_smallstep_match_zero:
  forall t v,
    t ~>* v ->
    cbv_value v ->
    forall tn t0 ts,
      t = tmatch tn t0 ts ->
      tn ~>* zero ->
      t0 ~>* v.
Proof.
  induction 1; repeat step || step_inversion cbv_value || t_invert_step || apply_any;
    eauto 3 using smallstep_succ_zero with exfalso;
    eauto using value_irred, star_one_step with values.
Qed.

Lemma star_smallstep_match_succ:
  forall t v v0 tn t0 ts,
    cbv_value v ->
    cbv_value v0 ->
    tn ~>* succ v ->
    t ~>* v0 ->
    open 0 ts v ~>* v0 ->
    tmatch tn t0 ts ~>* v0.
Proof.
  intros.
  eapply star_trans; eauto.
  eapply star_trans; eauto with cbvlemmas; eauto with smallstep star.
Qed.

Lemma star_smallstep_match_inv_succ:
  forall v v0 tn t0 ts,
    cbv_value v ->
    cbv_value v0 ->
    tn ~>* succ v ->
    tmatch tn t0 ts ~>* v0 ->
    open 0 ts v ~>* v0.
Proof.
  intros.
  eapply star_many_steps;
    eauto;
    eauto 5 using star_trans with cbvlemmas smallstep;
    eauto using value_irred.
Qed.

Lemma star_smallstep_match_inv:
  forall t v,
    t ~>* v ->
    cbv_value v ->
    forall tn t0 ts,
      t = tmatch tn t0 ts ->
      (
        tn ~>* zero /\ t0 ~>* v
        \/
        exists v',
          cbv_value v' /\
          tn ~>* succ v' /\
          open 0 ts v' ~>* v
      ).
Proof.
  induction 1; repeat step || step_inversion cbv_value || t_invert_step;
    eauto 6 with smallstep star.
Qed.

Lemma star_smallstep_tleft_inv:
  forall t v,
    t ~>* v ->
    cbv_value v ->
    forall t',
      t = tleft t' ->
      exists v',
        v = tleft v' /\
        cbv_value v' /\
        t' ~>* v'.
Proof.
  induction 1; repeat step || step_inversion cbv_value || t_invert_step;
    eauto with smallstep values cbvlemmas star.
Qed.

Lemma star_smallstep_tright_inv:
  forall t v,
    t ~>* v ->
    cbv_value v ->
    forall t',
      t = tright t' ->
      exists v',
        v = tright v' /\
        cbv_value v' /\
        t' ~>* v'.
Proof.
  induction 1; repeat step || step_inversion cbv_value || t_invert_step;
    eauto with smallstep values cbvlemmas star.
Qed.

Lemma star_smallstep_sum_match_inv:
  forall t v,
    t ~>* v ->
    cbv_value v ->
    forall t' tl tr,
      t = sum_match t' tl tr -> (
        (exists v', t' ~>* tleft v' /\ open 0 tl v' ~>* v) \/
        (exists v', t' ~>* tright v' /\ open 0 tr v' ~>* v)
      ).
Proof.
  induction 1; repeat step || step_inversion cbv_value || t_invert_step;
    eauto with smallstep values cbvlemmas star.
Qed.

Lemma star_smallstep_fix_inv:
  forall t v,
    notype_tfix t ~>* v ->
    cbv_value v ->
    open 0 (open 1 t zero) (notype_tfix t) ~>* v.
Proof.
  inversion 1; repeat step || step_inversion cbv_value || t_invert_step.
Qed.


Lemma star_smallstep_tsize_inv:
  forall t v,
    t ~>* v ->
    cbv_value v ->
    forall t',
      t = tsize t' ->
      is_nat_value v.
Proof.
  induction 1;
    repeat match goal with
           | H2: build_nat _ ~>* ?v2 |- _ =>
              unshelve epose proof (star_smallstep_value _ v2 H2 _); clear H2
           | _ => step || step_inversion cbv_value || t_invert_step
           end;
    eauto with smallstep values cbvlemmas;
    eauto using is_nat_value_build_nat with values.
Qed.

Lemma star_smallstep_tsize_inv2:
  forall t v,
    t ~>* v ->
    cbv_value v ->
    forall t', t = tsize t' ->
      exists v',
        t' ~>* v' /\
        cbv_value v' /\
        v = build_nat (tsize_semantics v').
Proof.
  induction 1;
    repeat match goal with
           | H2: build_nat _ ~>* ?v2 |- _ =>
              unshelve epose proof (star_smallstep_value _ v2 H2 _); clear H2
           | _ => step || step_inversion cbv_value || t_invert_step
           end;
    eauto 6 with smallstep values cbvlemmas star.
Qed.

Lemma star_smallstep_deterministic:
  forall t v,
    t ~>* v ->
    forall v',
      cbv_value v ->
      cbv_value v' ->
      t ~>* v' ->
      v = v'.
Proof.
  induction 1; steps; eauto using star_smallstep_value with smallstep.
  inversion H3; repeat step || deterministic_step || no_step.
Qed.

Lemma star_smallstep_app_onestep:
  forall t v1 v2,
    app (notype_lambda t) v1 ~>* v2 ->
    cbv_value v1 ->
    cbv_value v2 ->
    open 0 t v1 ~>* v2.
Proof.
  inversion 1; repeat step || step_inversion cbv_value scbv_step.
  inversion H0; repeat step || no_step.
Qed.

Ltac t_deterministic_star :=
    match goal with
    | H1: ?t ~>* ?v1,
      H2: ?t ~>* ?v2 |- _ =>
      poseNew (Mark (v1,v2) "equality");
      unshelve epose proof (star_smallstep_deterministic _ _ H1 _ _ _ H2)
    end; eauto with values.

Ltac t_invert_star :=
  match goal with
  | H: app ?t1 ?t2 ~>* ?v |- _ =>
    (tryif (not_cbv_value t1) then idtac else not_cbv_value t2);
    cbv_value v;
    poseNew (Mark H "inv app");
    unshelve epose proof (star_smallstep_app_inv _ v H _ t1 t2 eq_refl)

  | H2: pp ?t1 ?t2 ~>* ?v |- _ =>
    cbv_value v;
    (not_cbv_value t1 || not_cbv_value t2);
    poseNew (Mark H2 "inv pair");
    unshelve epose proof (star_smallstep_pp_inv _ v H2 _ t1 t2 eq_refl)

  | H2: binary_primitive ?o ?t1 ?t2 ~>* ?v |- _ =>
    cbv_value v;
    (not_cbv_value t1 || not_cbv_value t2);
    poseNew (Mark H2 "inv binary primitive");
    unshelve epose proof (star_smallstep_binary_primitive_inv _ v H2 _ t1 t2 o eq_refl)

  | H2: pi1 ?t ~>* ?v |- _ =>
    cbv_value v;
    poseNew (Mark H2 "inv pi1");
    unshelve epose proof (star_smallstep_pi1_inv _ v H2 _ t eq_refl)

  | H2: pi2 ?t ~>* ?v |- _ =>
    cbv_value v;
    poseNew (Mark H2 "inv pi2");
    unshelve epose proof (star_smallstep_pi2_inv _ v H2 _ t eq_refl)

  | H2: ite _ _ _ ~>* ?v |- _ =>
    cbv_value v;
    poseNew (Mark H2 "inv ite");
    unshelve epose proof (star_smallstep_ite_inv _ v H2 _ _ _ _ eq_refl)

  | H2: succ _ ~>* ?v |- _ =>
    cbv_value v;
    poseNew (Mark H2 "inv succ");
    unshelve epose proof (star_smallstep_succ_inv _ v H2 _ _ eq_refl)

  | H2: notype_tfix _ ~>* ?v |- _ =>
    cbv_value v;
    apply star_smallstep_fix_inv in H2

  | H2: tleft _ ~>* ?v |- _ =>
    cbv_value v;
    poseNew (Mark H2 "inv left");
    unshelve epose proof (star_smallstep_tleft_inv _ v H2 _ _ eq_refl)

  | H2: tright _ ~>* ?v |- _ =>
    cbv_value v;
    poseNew (Mark H2 "inv right");
    unshelve epose proof (star_smallstep_tright_inv _ v H2 _ _ eq_refl)

  | H2: tsize _ ~>* ?v |- _ =>
    cbv_value v;
    poseNew (Mark H2 "inv tsize");
    unshelve epose proof (star_smallstep_tsize_inv _ v H2 _ _ eq_refl)

  | H1: tmatch ?tn _ _ ~>* ?v,
    H2: ?tn ~>* zero |- _ =>
    cbv_value v;
    poseNew (Mark H1 "inv match");
    unshelve epose proof (star_smallstep_match_zero _ v H1 _ _ _ _ eq_refl H2)

  | H: tmatch zero _ _ ~>* ?v |- _ =>
    cbv_value v;
    poseNew (Mark H "inv match");
    unshelve epose proof (star_smallstep_match_zero _ v H _ _ _ _ eq_refl _)

  | H: tmatch _ _ _ ~>* ?v |- _ =>
    cbv_value v;
    poseNew (Mark H "inv match");
    unshelve epose proof (star_smallstep_match_inv _ v H _ _ _ _ eq_refl)

  | H: sum_match _ _ _ ~>* ?v |- _ =>
    cbv_value v;
    poseNew (Mark H "inv sum match");
    unshelve epose proof (star_smallstep_sum_match_inv _ v H _ _ _ _ eq_refl)

  | H: notype_err ~>* _ |- _ => inversion H; clear H
  | _ => t_invert_step || star_smallstep_value
  end.

Ltac star_smallstep_app_onestep :=
  match goal with
  | H: app (notype_lambda ?t) ?v1 ~>* ?v2 |- _ =>
    poseNew (Mark (t, v1, v2) "star_smallstep_app_onestep");
    unshelve epose proof (star_smallstep_app_onestep _ _ _ H _ _)
  end.

Lemma false_step:
  tfalse ~>* ttrue -> False.
Proof.
  inversion 1; repeat step || t_invert_step.
Qed.

Lemma star_smallstep_ite_inv_true:
  forall b t1 t2 v,
    cbv_value v ->
    ite b t1 t2 ~>* v ->
    b ~>* ttrue ->
    t1 ~>* v.
Proof.
  repeat step || t_invert_star || t_deterministic_star.
Qed.

Lemma star_smallstep_ite_inv_false:
  forall b t1 t2 v,
    cbv_value v ->
    ite b t1 t2 ~>* v ->
    b ~>* tfalse ->
    t2 ~>* v.
Proof.
  repeat step || t_invert_star || t_deterministic_star.
Qed.

Ltac t_invert_ite :=
  match goal with
  | H1: ite ?b ?t1 ?t2 ~>* ?v |- ?t1 ~>* ?v =>
      apply star_smallstep_ite_inv_true with b t2
  | H1: ite ?b ?t1 ?t2 ~>* ?v |- ?t2 ~>* ?v =>
      apply star_smallstep_ite_inv_false with b t1
  end.

Lemma star_pp:
  forall t t',
    t ~>* t' ->
    forall t1 t2, t = pp t1 t2 ->
      exists t1' t2', t'= pp t1' t2'.
Proof.
  induction 1; repeat step || t_invert_step; eauto.
Qed.

Lemma star_pp_succ:
  forall t1 t2 t,
    pp t1 t2 ~>* succ t ->
    False.
Proof.
  intros.
  pose proof (star_pp _ _ H); steps.
Qed.

Ltac reverse_once :=
  t_invert_star;
    repeat step || star_smallstep_value ||
           step_inversion cbv_value || star_smallstep_app_onestep.
