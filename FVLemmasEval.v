Require Import Termination.Sets.
Require Import Termination.Syntax.
Require Import Termination.Tactics.
Require Import Termination.SmallStep.
Require Import Termination.TermProperties.
Require Import Termination.FVLemmas.
Require Import Termination.ListUtils.
Require Import Termination.SizeLemmas.
Require Import Termination.StarRelation.
Require Import Termination.SetLemmas.

Require Import Coq.Strings.String.

Require Import Omega.

Require Import Equations.Equations.


Lemma nat_value_fv:
  forall v,
    is_nat_value v -> fv v = nil.
Proof.
  induction v; repeat step || t_listutils.
Qed.

Hint Immediate nat_value_fv: bfv.

Lemma fv_smallstep:
  forall t t',
    small_step t t' ->
    forall x,
      x ∈ fv t' ->
      x ∈ fv t.
Proof.
  induction 1;
    repeat match goal with
           | _  => step || t_listutils
           | _ => progress (unfold subset in * )
           | H: context[fv (open ?k ?t ?rep)] |- _ =>
             poseNew (Mark (k,t,rep) "fv_open");
             pose proof (fv_open t rep k)
           | H1: forall x, _ -> _, H2: _ |- _ => pose proof (H1 _ H2); clear H1
           end; eauto with bfv blistutils.
Qed.

Hint Resolve fv_smallstep: bfv.                       

Lemma fv_smallstep_subset:
  forall t t',
    small_step t t' ->
    subset (fv t') (fv t).
Proof.
  unfold subset; intros; eauto using fv_smallstep.
Qed.

Hint Resolve fv_smallstep_subset: bfv.                       

Lemma fv_smallstep_subset2:
  forall t t' S,
    subset (fv t) S ->
    small_step t t' ->
    subset (fv t') S.
Proof.
  intros; eauto using subset_transitive with bfv.
Qed.

Hint Resolve fv_smallstep_subset2: bfv.                       

Lemma fv_smallstep_nil:
  forall t t',
    small_step t t' ->
    fv t = nil ->
    fv t' = nil.
Proof.
  repeat step || rewrite <- empty_list_rewrite in *; eauto with bfv.
Qed.

Hint Resolve fv_smallstep_nil: bfv.

Lemma fv_star_smallstep:
  forall t t',
    star small_step t t' ->
    forall x,
      x ∈ fv t' ->
      x ∈ fv t.
Proof.
  induction 1; eauto using fv_smallstep.
Qed.

Hint Resolve fv_star_smallstep: bfv.

Lemma fv_star_smallstep_nil:
  forall t t',
    star small_step t t' ->
    fv t = nil ->
    fv t' = nil.
Proof.
  repeat step || rewrite <- empty_list_rewrite in *; eauto with bfv.
Qed.

Hint Resolve fv_star_smallstep_nil: bfv.
