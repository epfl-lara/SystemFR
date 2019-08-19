Require Import SystemFR.Equivalence.
Require Import SystemFR.Syntax.
Require Import SystemFR.Tactics.
Require Import SystemFR.StarInversions.
Require Import SystemFR.StarRelation.
Require Import SystemFR.SmallStep.
Require Import SystemFR.StarLemmas.

Require Import Coq.Strings.String.

Lemma equivalence_def:
  forall t1 t2 v,
    is_value v ->
    equivalent t1 t2 ->
    star small_step t1 v ->
    star small_step t2 v.
Proof.
  unfold equivalent; steps; eauto.
Qed.

Lemma equivalence_def2:
  forall t1 t2 v,
    is_value v ->
    equivalent t1 t2 ->
    star small_step t2 v ->
    star small_step t1 v.
Proof.
  unfold equivalent; steps; eauto.
Qed.

Lemma not_equivalent:
  equivalent tfalse ttrue -> False.
Proof.
  unfold equivalent; steps.
  unshelve epose proof (H0 ttrue _ _); repeat step || t_invert_star.
Qed.

Lemma equivalent_true:
  forall t, equivalent t ttrue ->
       star small_step t ttrue.
Proof.
  unfold equivalent; steps; eauto with smallstep values.
Qed.

Lemma equivalent_sym:
  forall t1 t2, equivalent t1 t2 -> equivalent t2 t1.
Proof.
  unfold equivalent; steps.
Qed.

Lemma equivalent_trans:
  forall t1 t2 t3,
    equivalent t1 t2 ->
    equivalent t2 t3 ->
    equivalent t1 t3
.
Proof.
  unfold equivalent; steps.
Qed.

Lemma equivalent_step:
  forall t1 t2, small_step t1 t2 -> equivalent t1 t2.
Proof.
  unfold equivalent; steps;
    eauto with smallstep;
    eauto using value_irred, star_one_step.
Qed.

Hint Resolve equivalent_step: b_equiv.

Lemma equivalent_star:
  forall t1 t2, star small_step t1 t2 -> equivalent t1 t2.
Proof.
  unfold equivalent; steps;
    eauto using star_smallstep_trans;
    eauto using value_irred, star_many_steps.
Qed.

Hint Resolve equivalent_star: b_equiv.

Lemma equivalent_refl:
  forall t, equivalent t t.
Proof.
  unfold equivalent; steps.
Qed.

Hint Resolve equivalent_refl: b_equiv.

Lemma equivalent_app_congr:
  forall t1 t2 t1' t2',
    equivalent t1' t2' ->
    equivalent t1 t2 ->
    equivalent (app t1 t1') (app t2 t2').
Proof.
  unfold equivalent in *; repeat step || t_invert_star;
    eauto 7 using star_smallstep_trans with bsteplemmas smallstep.
Qed.

Hint Resolve equivalent_app_congr: b_equiv.

Lemma equivalent_pi1_congr:
  forall t t',
    equivalent t t' ->
    equivalent (pi1 t) (pi1 t').
Proof.
  unfold equivalent in *; repeat step || t_invert_star;
    eauto 7 using star_smallstep_trans with bsteplemmas smallstep.
Qed.

Hint Resolve equivalent_pi1_congr: b_equiv.

Lemma equivalent_pi2_congr:
  forall t t',
    equivalent t t' ->
    equivalent (pi2 t) (pi2 t').
Proof.
  unfold equivalent in *; repeat step || t_invert_star;
    eauto 7 using star_smallstep_trans with bsteplemmas smallstep.
Qed.

Hint Resolve equivalent_pi2_congr: b_equiv.

Lemma equivalent_pp_congr:
  forall t1 t2 t1' t2',
    equivalent t1' t2' ->
    equivalent t1 t2 ->
    equivalent (pp t1 t1') (pp t2 t2').
Proof.
  unfold equivalent in *; repeat step || t_invert_star;
    eauto 7 using star_smallstep_trans with bsteplemmas smallstep.
Qed.

Hint Resolve equivalent_pp_congr: b_equiv.

Lemma equivalent_ite:
  forall t1 t2 t3 t,
    (star small_step t1 ttrue \/ star small_step t1 tfalse) ->
    (star small_step t1 ttrue -> equivalent t2 t) ->
    (star small_step t1 tfalse -> equivalent t3 t) ->
    equivalent (ite t1 t2 t3) t.
Proof.
  unfold equivalent in *; repeat step || t_invert_star;
    eauto 7 using star_smallstep_trans with bsteplemmas smallstep.
Qed.

Hint Resolve equivalent_ite: b_equiv.

Lemma equivalent_match:
  forall t v tn t0 ts,
    is_nat_value v ->
    star small_step tn v ->
    (v = zero -> equivalent t0 t) ->
    (forall v', v = succ v' -> equivalent (open 0 ts v') t) ->
    equivalent (tmatch tn t0 ts) t.
Proof.
  unfold equivalent in *; intros; inversion H; repeat step || t_invert_star;
    eauto using star_smallstep_trans with bsteplemmas smallstep;
    eauto 3 using star_smallstep_match_zero;
    eauto 4 using star_smallstep_match_succ, is_nat_value_value;
    eauto 4 using star_smallstep_match_inv_succ, is_nat_value_value.
Qed.

Hint Resolve equivalent_match: b_equiv.

Lemma equivalent_rec:
  forall t v tn t0 ts,
    is_nat_value v ->
    star small_step tn v ->
    (v = zero -> equivalent t0 t) ->
    (forall v', v = succ v' ->
           equivalent (open 0 (open 1 ts v') (notype_lambda (notype_rec v' t0 ts)))
                      t) ->
    equivalent (notype_rec tn t0 ts) t.
Proof.
  unfold equivalent in *; intros; inversion H; repeat step || t_invert_star;
    eauto using star_smallstep_trans with bsteplemmas smallstep;
    eauto 3 using star_smallstep_rec_zero2;
    eauto 4 using star_smallstep_rec_succ2, is_nat_value_value;
    eauto 4 using star_smallstep_rec_inv_succ2, is_nat_value_value.
Qed.

Hint Resolve equivalent_rec: b_equiv.


Lemma equivalent_succ_congr:
  forall e1 e2,
    equivalent e1 e2 ->
    equivalent (succ e1) (succ e2).
Proof.
  unfold equivalent in *; repeat step || t_invert_star;
    eauto 3 using star_smallstep_trans with bsteplemmas smallstep.
Qed.

Hint Resolve equivalent_succ_congr: b_equiv.

Lemma equivalent_succ_inj:
  forall e1 e2,
    equivalent (succ e1) (succ e2) ->
    equivalent e1 e2.
Proof.
  unfold equivalent in *;
    repeat match goal with
           | _ => step
           | H: forall v, is_value v -> star small_step (succ ?e) v -> _,
             H1: star small_step ?e ?v |- _ =>
              poseNew (Mark 0 "inst");
              unshelve epose proof (H (succ v) _ _)
           |  H: star small_step (succ _) ?v |- _ =>
              poseNew (Mark H "inv succ");
              unshelve epose proof (star_smallstep_succ_inv _ v H _ _ eq_refl)
          end;
    eauto with values;
    eauto with bsteplemmas.
Qed.

Hint Resolve equivalent_succ_inj: b_equiv.

Lemma equivalent_ite_true:
  forall b e1 e2,
    star small_step b ttrue ->
    equivalent (ite b e1 e2) e1.
Proof.
  unfold equivalent in *; repeat step || t_invert_star || t_deterministic_star;
    eauto using star_smallstep_trans with bsteplemmas smallstep.
Qed.

Lemma equivalent_ite_true2:
  forall b e1 e2 e,
    star small_step b ttrue ->
    equivalent e1 e ->
    equivalent (ite b e1 e2) e.
Proof.
  unfold equivalent in *; repeat step || t_invert_star || t_deterministic_star;
    eauto using star_smallstep_trans with bsteplemmas smallstep.
Qed.


Lemma equivalent_ite_true3:
  forall b e1 e2 e,
    star small_step b ttrue ->
    equivalent (ite b e1 e2) e ->
    equivalent e1 e.
Proof.
  steps.
  eauto using equivalent_ite_true, equivalent_sym, equivalent_trans.
Qed.

Lemma equivalent_ite_false:
  forall b e1 e2,
    star small_step b tfalse ->
    equivalent (ite b e1 e2) e2.
Proof.
  unfold equivalent in *; repeat step || t_invert_star || t_deterministic_star;
    eauto using star_smallstep_trans with bsteplemmas smallstep.
Qed.

Lemma equivalent_ite_false2:
  forall b e1 e2 e,
    star small_step b tfalse ->
    equivalent (ite b e1 e2) e ->
    equivalent e2 e.
Proof.
  eauto using equivalent_ite_false, equivalent_sym, equivalent_trans.
Qed.

Lemma equivalent_ite_false3:
  forall b e1 e2 e,
    star small_step b tfalse ->
    equivalent (ite b e1 e2) e ->
    equivalent e2 e.
Proof.
  steps.
  eauto using equivalent_ite_false, equivalent_sym, equivalent_trans.
Qed.

Hint Resolve equivalent_ite_true: b_equiv.
Hint Resolve equivalent_ite_true2: b_equiv.
Hint Resolve equivalent_ite_true3: b_equiv.
Hint Resolve equivalent_ite_false: b_equiv.
Hint Resolve equivalent_ite_false2: b_equiv.
Hint Resolve equivalent_ite_false3: b_equiv.

Lemma equivalent_ites_true:
  forall b u1 v1 u2 v2,
    star small_step b ttrue ->
    equivalent (ite b u1 u2) (ite b v1 v2) ->
    equivalent u1 v1.
Proof.
  eauto 4 using equivalent_trans, equivalent_sym with b_equiv.
Qed.

Hint Immediate equivalent_ites_true: b_equiv.

Lemma equivalent_ites_true2:
  forall b u1 v1 u2 v2,
    star small_step b ttrue ->
    equivalent u1 v1 ->
    equivalent (ite b u1 u2) (ite b v1 v2).
Proof.
  eauto 4 using equivalent_trans, equivalent_sym with b_equiv.
Qed.

Hint Immediate equivalent_ites_true2: b_equiv.

Lemma equivalent_ites_false:
  forall b u1 v1 u2 v2,
    star small_step b tfalse ->
    equivalent (ite b u1 u2) (ite b v1 v2) ->
    equivalent u2 v2.
Proof.
  eauto 4 using equivalent_trans, equivalent_sym with b_equiv.
Qed.

Hint Immediate equivalent_ites_false: b_equiv.

Lemma equivalent_ites_false2:
  forall b u1 v1 u2 v2,
    star small_step b tfalse ->
    equivalent u2 v2 ->
    equivalent (ite b u1 u2) (ite b v1 v2).
Proof.
  eauto 5 using equivalent_trans, equivalent_sym with b_equiv.
Qed.

Hint Immediate equivalent_ites_false2: b_equiv.

Lemma equivalent_match_zero:
  forall n e1 e2,
    star small_step n zero ->
    equivalent (tmatch n e1 e2) e1.
Proof.
  unfold equivalent in *; repeat step || t_deterministic_star || t_invert_star;
    eauto using star_smallstep_trans with bsteplemmas smallstep.
Qed.

Hint Resolve equivalent_match_zero: b_equiv.

Lemma equivalent_match_zero2:
  forall n e1 e2 e,
    star small_step n zero ->
    equivalent (tmatch n e1 e2) e ->
    equivalent e1 e.
Proof.
  eauto using equivalent_match_zero, equivalent_sym, equivalent_trans.
Qed.

Hint Resolve equivalent_match_zero2: b_equiv.

Lemma equivalent_match_succ:
  forall n e1 e2 v,
    is_value v ->
    star small_step n (succ v) ->
    equivalent (tmatch n e1 e2) (open 0 e2 v).
Proof.
  unfold equivalent in *; repeat step || t_invert_star || t_deterministic_star;
    eauto using star_smallstep_trans with bsteplemmas smallstep.
Qed.

Hint Resolve equivalent_match_succ: b_equiv.

Lemma equivalent_match_succ2:
  forall n e1 e2 v e,
    is_nat_value v ->
    star small_step n (succ v) ->
    equivalent (tmatch n e1 e2) e ->
    equivalent (open 0 e2 v) e.
Proof.
  intros.
  eauto using is_nat_value_value, equivalent_match_succ, equivalent_sym, equivalent_trans.
Qed.

Hint Resolve equivalent_match_succ2: b_equiv.
