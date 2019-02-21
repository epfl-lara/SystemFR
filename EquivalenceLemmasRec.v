Require Import Termination.Syntax.
Require Import Termination.Tactics.
Require Import Termination.StarInversions.
Require Import Termination.StarRelation.
Require Import Termination.SmallStep.
Require Import Termination.StarLemmas.

Require Import Termination.Equivalence.
Require Import Termination.EquivalenceLemmas.

Lemma equivalent_rec_zero:
  forall n e1 e2,
    star small_step n zero ->
    equivalent (notype_rec n e1 e2) e1.
Proof.
  unfold equivalent in *; repeat step || t_invert_star || t_deterministic_star;
    eauto using star_smallstep_trans with bsteplemmas smallstep.
Qed.

Hint Resolve equivalent_rec_zero: b_equiv.

Lemma equivalent_rec_zero2:
  forall n e1 e2 e,
    star small_step n zero ->
    equivalent (notype_rec n e1 e2) e ->
    equivalent e1 e.
Proof.
  eauto using equivalent_rec_zero, equivalent_sym, equivalent_trans.
Qed.

Hint Resolve equivalent_rec_zero2: b_equiv.

Lemma equivalent_rec_succ:
  forall n e1 e2 v,
    is_value v ->
    star small_step n (succ v) ->
    equivalent (notype_rec n e1 e2) (open 0 (open 1 e2 v)
                                       (notype_lambda (notype_rec v e1 e2))).
Proof.
  unfold equivalent in *; repeat step || t_invert_star || t_deterministic_star;
    eauto using star_smallstep_trans with bsteplemmas smallstep.
Qed.

Hint Resolve equivalent_rec_succ: b_equiv.

Lemma equivalent_rec_succ2:
  forall n e1 e2 v e,
    is_nat_value v ->
    star small_step n (succ v) ->
    equivalent (notype_rec n e1 e2) e ->
    equivalent  (open 0 (open 1 e2 v) (notype_lambda (notype_rec v e1 e2))) e.
Proof.
  intros.
  eauto using is_nat_value_value, equivalent_rec_succ, equivalent_sym, equivalent_trans.
Qed.

Hint Resolve equivalent_rec_succ2: b_equiv.
