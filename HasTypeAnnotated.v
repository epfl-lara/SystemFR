Require Import Termination.TypeErasure.
Require Import Termination.TypeErasureLemmas.
Require Import Termination.Syntax.
Require Import Termination.Trees.
Require Import Termination.TreeLists.
Require Import Termination.Typing.
Require Import Termination.Tactics.
Require Import Termination.Sets.
Require Import Termination.AssocList.

Lemma annotated_term_type:
  forall t,
    is_annotated_term t ->
    is_annotated_type t ->
    False.
Proof.
  destruct t; steps.
Qed.

Lemma annotated_open:
  forall t k rep,
    (is_annotated_term (open k t rep) -> is_annotated_term rep -> is_annotated_term t) /\
    (is_annotated_type (open k t rep) -> is_annotated_term rep -> is_annotated_type t).
Proof.
  induction t;
    try solve [ repeat step || eapply_any; eauto using annotated_term_type with falsity ].
Qed.

Lemma annotated_open_1:
  forall t k rep,
    is_annotated_term (open k t rep) ->
    is_annotated_term rep ->
    is_annotated_term t.
Proof.
  apply annotated_open.
Qed.

Lemma annotated_open_2:
  forall T k rep,
    is_annotated_type (open k T rep) ->
    is_annotated_term rep ->
    is_annotated_type T.
Proof.
  apply annotated_open.
Qed.

Hint Resolve annotated_open_1: bannot.
Hint Resolve annotated_open_2: bannot.

Ltac t_annotated_open :=
  match goal with
  | H: is_annotated_term (open ?k ?t ?rep) |- is_annotated_term ?t =>
      apply annotated_open with k rep
  | H: is_annotated_term (open _ (open ?k ?t ?rep) _) |- is_annotated_term ?t =>
      poseNew (Mark 0 "once");
      apply annotated_open with k rep
  | H: is_annotated_type (open ?k ?t ?rep) |- is_annotated_type ?t =>
      apply annotated_open with k rep
  end.

Lemma annotations:
  (forall tvars gamma t T,
    has_type tvars gamma t T ->
    (annotated_types gamma /\ is_annotated_term t /\ is_annotated_type T)
  ) /\
  (forall tvars gamma T,
    is_type tvars gamma T ->
    (annotated_types gamma /\ is_annotated_type T)
  ) /\
  (forall tvars gamma,
    is_context tvars gamma ->
    annotated_types gamma
  ) /\
  (forall tvars gamma T1 T2,
    is_subtype tvars gamma T1 T2 ->
    (annotated_types gamma /\ is_annotated_type T1 /\ is_annotated_type T2)
  ) /\
  (forall tvars gamma t1 t2,
    are_equal tvars gamma t1 t2 ->
    (annotated_types gamma /\ is_annotated_term t1 /\ is_annotated_term t2)
  )
.
Proof.
  apply mut_HT_IT_IC_IS_AE;
    try solve [
      repeat step || t_annotated_open || rewrite annotated_types_append in *;
      eauto with bannot
    ].
Qed.

Ltac t_annotations :=
  match goal with
  | H: has_type ?tvars ?gamma ?t ?T |- _ =>
    poseNew (Mark (gamma, t, T) "annotations");
    pose proof ((proj1 annotations) tvars gamma t T H)
  | H: is_type ?tvars ?gamma ?T |- _ =>
    poseNew (Mark (gamma, T) "annotations");
    pose proof ((proj1 (proj2 annotations)) tvars gamma T H)
  end.

Lemma has_type_annot_1:
  forall tvars gamma t T,
    has_type tvars gamma t T ->
    annotated_types gamma.
Proof.
  apply annotations.
Qed.

Lemma has_type_annot_2:
  forall tvars gamma t T,
    has_type tvars gamma t T ->
    is_annotated_term t.
Proof.
  apply annotations.
Qed.

Lemma has_type_annot_3:
  forall tvars gamma t T,
    has_type tvars gamma t T ->
    is_annotated_type T.
Proof.
  apply annotations.
Qed.

Lemma is_type_annot_1:
  forall tvars gamma T,
    is_type tvars gamma T ->
    annotated_types gamma.
Proof.
  apply annotations.
Qed.

Lemma is_type_annot_2:
  forall tvars gamma T,
    is_type tvars gamma T ->
    is_annotated_type T.
Proof.
  apply annotations.
Qed.

Lemma is_subtype_annot_1:
  forall tvars gamma T1 T2,
    is_subtype tvars gamma T1 T2 ->
    annotated_types gamma.
Proof.
  apply annotations.
Qed.

Lemma is_subtype_annot_2:
  forall tvars gamma T1 T2,
    is_subtype tvars gamma T1 T2 ->
    is_annotated_type T1.
Proof.
  apply annotations.
Qed.

Lemma is_subtype_annot_3:
  forall tvars gamma T1 T2,
    is_subtype tvars gamma T1 T2 ->
    is_annotated_type T2.
Proof.
  apply annotations.
Qed.

Lemma is_context_annot:
  forall tvars gamma,
    is_context tvars gamma ->
    annotated_types gamma.
Proof.
  apply annotations.
Qed.

Lemma are_equal_annot_1:
  forall tvars gamma t1 t2,
    are_equal tvars gamma t1 t2 ->
    annotated_types gamma.
Proof.
  apply annotations.
Qed.

Lemma are_equal_annot_2:
  forall tvars gamma t1 t2,
    are_equal tvars gamma t1 t2 ->
    is_annotated_term t1.
Proof.
  apply annotations.
Qed.

Lemma are_equal_annot_3:
  forall tvars gamma t1 t2,
    are_equal tvars gamma t1 t2 ->
    is_annotated_term t2.
Proof.
  apply annotations.
Qed.


Hint Resolve has_type_annot_1: bannot.
Hint Resolve has_type_annot_2: bannot.
Hint Resolve has_type_annot_3: bannot.
Hint Resolve is_subtype_annot_1: bannot.
Hint Resolve is_subtype_annot_2: bannot.
Hint Resolve is_subtype_annot_3: bannot.
Hint Resolve are_equal_annot_1: bannot.
Hint Resolve are_equal_annot_2: bannot.
Hint Resolve are_equal_annot_3: bannot.
Hint Resolve is_type_annot_1: bannot.
Hint Resolve is_type_annot_2: bannot.
Hint Resolve is_context_annot: bannot.

Ltac t_context_annotations :=
  match goal with
  | H: has_type ?tvars ?gamma ?t ?T |- _ =>
    poseNew (Mark (gamma, t, T) "context_annotations");
    pose proof (has_type_annot_1 tvars gamma t T H)
  | H: is_type ?tvars ?gamma ?T |- _ =>
    poseNew (Mark (gamma, T) "context_annotations");
    pose proof (is_type_annot_1 tvars gamma T H)
  | H: are_equal ?tvars ?gamma ?t1 ?t2 |- _ =>
    poseNew (Mark (gamma, t1, t2) "context_annotations");
    pose proof (are_equal_annot_1 tvars gamma t1 t2 H)
  | H: is_subtype ?tvars ?gamma ?T1 ?T2 |- _ =>
    poseNew (Mark (gamma, T1, T2) "context_annotations");
    pose proof (is_subtype_annot_1 tvars gamma T1 T2 H)
  | H: is_context ?tvars ?gamma |- _ =>
    poseNew (Mark (gamma) "context_annotations");
    pose proof (is_context_annot tvars gamma H)
  end.
