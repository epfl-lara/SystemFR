Require Export SystemFR.WFLemmas.
Require Export SystemFR.BaseType.
Require Export SystemFR.Tactics.
Require Export SystemFR.TWFLemmas.
Require Export SystemFR.AnnotatedTermLemmas.
Require Export SystemFR.Trees.
Require Export SystemFR.Syntax.

Require Export SystemFR.ListUtils.

Lemma wf_base_type:
  forall X A B,
    base_type X A B ->
    forall k,
      wf A k ->
      wf B k.
Proof.
  induction 1; steps.
Qed.

#[global]
Hint Immediate wf_base_type: wf.

Ltac t_wf_base_type :=
  match goal with
  | H: base_type ?X ?A ?B |- wf ?B ?k => apply wf_base_type with X A
  end.

#[global]
Hint Extern 50 => t_wf_base_type: wf.

Lemma twf_base_type:
  forall X A B,
    base_type X A B ->
    forall k,
      twf A k ->
      twf B k.
Proof.
  induction 1; steps.
Qed.

#[global]
Hint Immediate twf_base_type: twf.

Ltac t_twf_base_type :=
  match goal with
  | H: base_type ?X ?A ?B |- twf ?B ?k => apply twf_base_type with X A
  end.

#[global]
Hint Extern 50 => t_twf_base_type: twf.

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

#[global]
Hint Extern 50 => t_annotated_base_type: annot.

Lemma pfv_base_type:
  forall X A B,
    base_type X A B ->
    forall x tag,
      x ∈ pfv B tag ->
      x ∈ pfv A tag.
Proof.
  induction 1; repeat step || list_utils.
Qed.

Ltac t_pfv_base_type :=
  match goal with
  | H1: base_type ?X ?A ?B, H2: ?Y ∈ pfv ?B ?tag |- _ => apply (pfv_base_type _ _ _ H1) in H2
  end.

#[global]
Hint Extern 50 => t_pfv_base_type: fv.

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
  induction 1; repeat step || list_utils.
Qed.

#[global]
Hint Extern 1000 => apply False_ind; eapply pfv_base_type2; eassumption: fv.
