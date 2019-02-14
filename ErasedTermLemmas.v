Require Import Termination.Syntax.
Require Import Termination.Tactics.
Require Import Termination.WFLemmas.
Require Import Termination.TWFLemmas.
Require Import Termination.ListUtils.
Require Import Termination.SmallStep.
Require Import Termination.StarRelation.
Require Import Termination.SubstitutionLemmas.
Require Import Termination.PrimitiveSize.

Lemma is_erased_term_twf:
  forall t k,
    is_erased_term t ->
    twf t k.
Proof.
  induction t; steps.
Qed.

Hint Resolve is_erased_term_twf: btwf.

Lemma is_erased_open:
  forall t k rep,
    is_erased_term t ->
    is_erased_term rep ->
    is_erased_term (open k t rep).
Proof.
  induction t; steps.
Qed.

Hint Resolve is_erased_open: berased.

Lemma is_erased_type_open:
  forall t k rep,
    is_erased_type t ->
    is_erased_term rep ->
    is_erased_type (open k t rep).
Proof.
  induction t; steps; eauto with berased.
Qed.

Hint Resolve is_erased_type_open: berased.

Lemma is_erased_type_topen:
  forall t k rep,
    is_erased_type t ->
    is_erased_type rep ->
    is_erased_type (topen k t rep).
Proof.
  induction t; repeat step || rewrite topen_none by eauto with btwf.
Qed.

Hint Resolve is_erased_type_topen: berased.

Lemma is_erased_open2:
  forall t k rep,
    is_erased_term (open k t rep) ->
    is_erased_term t.
Proof.
  induction t; steps; eauto.
Qed.

Lemma is_erased_term_tfv:
  forall t,
    is_erased_term t ->
    pfv t type_var = nil.
Proof.
  induction t; repeat step || t_listutils.
Qed.

Hint Resolve is_erased_term_tfv: bfv.

Lemma is_erased_topen:
  forall t k rep,
    is_erased_term t ->
    is_erased_term rep ->
    is_erased_term (topen k t rep).
Proof.
  induction t; steps.
Qed.

Hint Resolve is_erased_topen: berased.

Lemma is_erased_topen2:
  forall t k rep,
    is_annotated_term t ->
    is_erased_term (topen k t rep) ->
    is_erased_term t.
Proof.
  induction t; steps; eauto.
Qed.

Lemma is_erased_term_tsize:
  forall n, is_erased_term (build_nat n).
Proof.
  eauto using is_nat_value_erased, is_nat_value_build_nat.
Qed.

Hint Resolve is_erased_term_tsize: berased.

Lemma erase_smallstep:
  forall t1 t2,
    small_step t1 t2 ->
    is_erased_term t1 ->
    is_erased_term t2.
Proof.
  induction 1; steps; eauto 3 using is_erased_open with step_tactic;
    eauto with berased.
Qed.

Hint Immediate erase_smallstep: berased.

Lemma erase_star_smallstep:
  forall t1 t2,
    star small_step t1 t2 ->
    is_erased_term t1 ->
    is_erased_term t2.
Proof.
  induction 1; steps; eauto using erase_smallstep.
Qed.

Hint Immediate erase_star_smallstep: berased.

Lemma is_erased_subst:
  forall t l,
    is_erased_term t ->
    psubstitute t l type_var = t.
Proof.
  intros; rewrite substitute_nothing5; eauto with bfv.
Qed.
