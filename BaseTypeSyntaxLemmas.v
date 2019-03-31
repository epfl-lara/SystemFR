Require Import Termination.WellFormed.
Require Import Termination.WFLemmas.
Require Import Termination.BaseType.
Require Import Termination.Tactics.
Require Import Termination.TWFLemmas.
Require Import Termination.AnnotatedTermLemmas.
Require Import Termination.Trees.
Require Import Termination.Syntax.
Require Import Termination.Sets.
Require Import Termination.ListUtils.

Lemma wf_base_type:
  forall X A B,
    base_type X A B ->
    forall k,
      wf A k ->
      wf B k.
Proof.
  induction 1; steps.
Qed.

Hint Immediate wf_base_type: bwf.

Ltac t_wf_base_type :=
  match goal with
  | H: base_type ?X ?A ?B |- wf ?B ?k => apply wf_base_type with X A
  end.

Hint Extern 50 => t_wf_base_type: bwf.

Lemma twf_base_type:
  forall X A B,
    base_type X A B ->
    forall k,
      twf A k ->
      twf B k.
Proof.
  induction 1; steps.
Qed.

Hint Immediate twf_base_type: tbwf.

Ltac t_twf_base_type :=
  match goal with
  | H: base_type ?X ?A ?B |- twf ?B ?k => apply twf_base_type with X A
  end.

Hint Extern 50 => t_twf_base_type: btwf.

Lemma annotated_base_type:
  forall X A B,
    base_type X A B ->
    is_annotated_type A ->
    is_annotated_type B.
Proof.
  induction 1; steps.
Qed.

Ltac t_annotated_base_type :=
  match goal with
  | H: base_type ?X ?A ?B |- is_annotated_type ?B => apply annotated_base_type with X A
  end.

Hint Extern 50 => t_annotated_base_type: bannot.

Lemma pfv_base_type:
  forall X A B,
    base_type X A B ->
    forall x tag,
      x ∈ pfv B tag ->
      x ∈ pfv A tag.
Proof.
  induction 1; repeat step || t_listutils.
Qed.

Ltac t_pfv_base_type :=
  match goal with
  | H1: base_type ?X ?A ?B, H2: ?Y ∈ pfv ?B ?tag |- _ => apply (pfv_base_type _ _ _ H1) in H2
  end.

Hint Extern 50 => t_pfv_base_type: bfv.

Lemma pfv_base_type_subset:
  forall X A B,
    base_type X A B ->
    forall S tag,
      subset (pfv A tag) S ->
      subset (pfv B tag) S.
Proof.
  unfold subset; steps; eauto using pfv_base_type.
Qed.

Ltac t_pfv_base_type_subset :=
  match goal with
  | H: base_type ?X ?A ?B |- subset (pfv ?B ?tag) ?S =>
      apply (pfv_base_type_subset _ _ _ H S tag)
  end.

Lemma pfv_base_type2:
  forall X A B,
    base_type X A B ->
    X ∈ pfv B type_var ->
    False.
Proof.
  induction 1; repeat step || t_listutils.
Qed.

Hint Extern 1000 => apply False_ind; eapply pfv_base_type2; eassumption: bfv.
