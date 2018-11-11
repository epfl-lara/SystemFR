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
  forall v tag,
    is_nat_value v -> pfv v tag = nil.
Proof.
  induction v; repeat step || t_listutils.
Qed.

Hint Immediate nat_value_fv: bfv.

Lemma fv_smallstep:
  forall t t',
    small_step t t' ->
    forall x tag,
      x ∈ pfv t' tag ->
      x ∈ pfv t tag.
Proof.
  induction 1;
    repeat step || t_listutils || t_fv_open || unfold subset in *;
    eauto with bfv blistutils.
Qed.

Hint Resolve fv_smallstep: bfv.                       

Lemma fv_smallstep_subset:
  forall t t' tag,
    small_step t t' ->
    subset (pfv t' tag) (pfv t tag).
Proof.
  unfold subset; intros; eauto using fv_smallstep.
Qed.

Hint Resolve fv_smallstep_subset: bfv.                       

Lemma fv_smallstep_subset2:
  forall t t' S tag,
    subset (pfv t tag) S ->
    small_step t t' ->
    subset (pfv t' tag) S.
Proof.
  intros; eauto using subset_transitive with bfv.
Qed.

Hint Resolve fv_smallstep_subset2: bfv.                       

Lemma fv_smallstep_nil:
  forall t t' tag,
    small_step t t' ->
    pfv t tag = nil ->
    pfv t' tag = nil.
Proof.
  repeat step || rewrite <- empty_list_rewrite in *; eauto with bfv.
Qed.

Hint Resolve fv_smallstep_nil: bfv.

Lemma fv_star_smallstep:
  forall t t',
    star small_step t t' ->
    forall x tag,
      x ∈ pfv t' tag ->
      x ∈ pfv t tag.
Proof.
  induction 1; eauto using fv_smallstep.
Qed.

Hint Resolve fv_star_smallstep: bfv.

Lemma fv_star_smallstep_nil:
  forall t t' tag,
    star small_step t t' ->
    pfv t tag = nil ->
    pfv t' tag = nil.
Proof.
  repeat step || rewrite <- empty_list_rewrite in *; eauto with bfv.
Qed.

Hint Resolve fv_star_smallstep_nil: bfv.
