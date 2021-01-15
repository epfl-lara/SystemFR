Require Import Coq.Strings.String.
Require Import Equations.Equations.

Require Export SystemFR.FVLemmas.
Require Export SystemFR.SmallStep.
Require Export SystemFR.SizeLemmas.
Require Export SystemFR.PrimitiveSize.
Require Export SystemFR.PrimitiveRecognizers.

Lemma nat_value_fv:
  forall v tag,
    is_nat_value v -> pfv v tag = nil.
Proof.
  induction 1;
    repeat step || list_utils.
Qed.

#[global]
Hint Immediate nat_value_fv: fv.

Lemma pfv_build_nat:
  forall n tag,
    pfv (build_nat n) tag = nil.
Proof.
  induction n; steps.
Qed.

#[global]
Hint Immediate pfv_build_nat: fv.

Lemma is_pair_fv:
  forall v tag,
    pfv (is_pair v) tag = nil.
Proof.
  destruct v; steps.
Qed.

#[global]
Hint Immediate is_pair_fv: fv.
Hint Rewrite is_pair_fv: rfv.

Lemma is_succ_fv:
  forall v tag,
    pfv (is_succ v) tag = nil.
Proof.
  destruct v; steps.
Qed.

#[global]
Hint Immediate is_succ_fv: fv.
Hint Rewrite is_succ_fv: rfv.

Lemma is_lambda_fv:
  forall v tag,
    pfv (is_lambda v) tag = nil.
Proof.
  destruct v; steps.
Qed.

#[global]
Hint Immediate is_lambda_fv: fv.
Hint Rewrite is_lambda_fv: rfv.

Lemma fv_smallstep:
  forall t t',
    t ~> t' ->
    forall x tag,
      x ∈ pfv t' tag ->
      x ∈ pfv t tag.
Proof.
  induction 1;
    repeat step || list_utils || fv_open || unfold subset in * ||
           (rewrite nat_value_fv in * by eauto using is_nat_value_build_nat) ||
           (autorewrite with rfv in *);
    eauto with fv list_utils.
Qed.

#[global]
Hint Immediate fv_smallstep: fv.

Lemma fv_smallstep_subset:
  forall t t' tag,
    t ~> t' ->
    subset (pfv t' tag) (pfv t tag).
Proof.
  unfold subset; intros; eauto using fv_smallstep.
Qed.

#[global]
Hint Resolve fv_smallstep_subset: fv.

Lemma fv_smallstep_subset2:
  forall t t' S tag,
    subset (pfv t tag) S ->
    t ~> t' ->
    subset (pfv t' tag) S.
Proof.
  intros; eauto using subset_transitive with fv.
Qed.

#[global]
Hint Immediate fv_smallstep_subset2: fv.

Lemma fv_smallstep_nil:
  forall t t' tag,
    t ~> t' ->
    pfv t tag = nil ->
    pfv t' tag = nil.
Proof.
  repeat step || rewrite <- empty_list_rewrite in *; eauto with fv.
Qed.

#[global]
Hint Immediate fv_smallstep_nil: fv.

Lemma fv_star_smallstep:
  forall t t',
    t ~>* t' ->
    forall x tag,
      x ∈ pfv t' tag ->
      x ∈ pfv t tag.
Proof.
  induction 1; eauto using fv_smallstep.
Qed.

#[global]
Hint Immediate fv_star_smallstep: fv.

Lemma fv_star_smallstep_nil:
  forall t t' tag,
    t ~>* t' ->
    pfv t tag = nil ->
    pfv t' tag = nil.
Proof.
  repeat step || rewrite <- empty_list_rewrite in *; eauto with fv.
Qed.

#[global]
Hint Immediate fv_star_smallstep_nil: fv.
