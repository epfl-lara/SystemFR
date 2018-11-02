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

Lemma annotated_topen:
  forall t k rep,
    (is_annotated_term (topen k t rep) -> is_annotated_type rep -> is_annotated_term t) /\
    (is_annotated_type (topen k t rep) -> is_annotated_type rep -> is_annotated_type t).
Proof.
  induction t;
    try solve [ repeat step || eapply_any; eauto using annotated_term_type with falsity ].
Qed.

Lemma annotated_topen_1:
  forall t k rep,
    is_annotated_term (topen k t rep) ->
    is_annotated_type rep ->
    is_annotated_term t.
Proof.
  apply annotated_topen.
Qed.

Lemma annotated_topen_2:
  forall T k rep,
    is_annotated_type (topen k T rep) ->
    is_annotated_type rep ->
    is_annotated_type T.
Proof.
  apply annotated_topen.
Qed.

Hint Resolve annotated_topen_1: bannot.
Hint Resolve annotated_topen_2: bannot.

Lemma annotated_open_build:
  forall t k rep,
    (is_annotated_type t -> is_annotated_term rep -> is_annotated_type (open k t rep)) /\
    (is_annotated_term t -> is_annotated_term rep -> is_annotated_term (open k t rep)).
Proof.
  induction t; repeat step || eapply_any.
Qed.

Hint Extern 50 => apply annotated_open_build: bannot.

Lemma annotated_topen_build:
  forall t k V,
    (is_annotated_type t -> is_annotated_type V -> is_annotated_type (topen k t V)) /\
    (is_annotated_term t -> is_annotated_type V -> is_annotated_term (topen k t V)).
Proof.
  induction t; repeat step || eapply_any.
Qed.

Hint Extern 50 => apply annotated_topen_build: bannot.

Ltac t_annotated_open :=
  match goal with
  | H: is_annotated_term (open ?k ?t ?rep) |- is_annotated_term ?t =>
      apply annotated_open with k rep
  | H: is_annotated_term (open _ (open ?k ?t ?rep) _) |- is_annotated_term ?t =>
      poseNew (Mark 0 "once");
      apply annotated_open with k rep
  | H: is_annotated_type (open ?k ?t ?rep) |- is_annotated_type ?t =>
      apply annotated_open with k rep
  | H: is_annotated_term (topen ?k ?t ?rep) |- is_annotated_term ?t =>
      apply annotated_topen with k rep
  | H: is_annotated_type (topen ?k ?t ?rep) |- is_annotated_type ?t =>
      apply annotated_topen with k rep
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
      repeat step || t_annotated_open || rewrite annotated_types_append in * ||
      unshelve eauto with bannot
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
  | H: is_subtype ?tvars ?gamma ?T1 ?T2  |- _ =>
    poseNew (Mark (gamma, T1, T2) "annotations");
    pose proof ((proj1 (proj2 (proj2 (proj2 annotations)))) tvars gamma T1 T2 H)
  | H: are_equal ?tvars ?gamma ?t1 ?t2  |- _ =>
    poseNew (Mark (gamma, t1, t2) "annotations");
    pose proof ((proj2 (proj2 (proj2 (proj2 annotations)))) tvars gamma t1 t2 H)
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

Lemma has_type_open_annot_1:
  forall tvars gamma t T k x,
    has_type tvars gamma (open k t (fvar x term_var)) T ->
    is_annotated_term t.
Proof.
  repeat step || t_annotations; eauto 2 with step_tactic bannot.
Qed.

Lemma has_type_open2_annot_1:
  forall tvars gamma t T i j x y,
    has_type tvars gamma (open i (open j t (fvar y term_var)) (fvar x term_var)) T ->
    is_annotated_term t.
Proof.
  repeat step || t_annotations; eauto 3 with step_tactic bannot.
Qed.

Lemma has_type_open_annot_2:
  forall tvars gamma t T k x,
    has_type tvars gamma t (open k T (fvar x term_var)) ->
    is_annotated_type T.
Proof.
  repeat step || t_annotations; eauto 2 with step_tactic bannot.
Qed.

Lemma has_type_open_annot_2_rep:
  forall tvars gamma t T k rep,
    is_annotated_term rep ->
    has_type tvars gamma t (open k T rep) ->
    is_annotated_type T.
Proof.
  repeat step || t_annotations; eauto 2 with step_tactic bannot.
Qed.

Lemma is_type_open_annot:
  forall tvars gamma T k x,
    is_type tvars gamma (open k T (fvar x term_var)) ->
    is_annotated_type T.
Proof.
  repeat step || t_annotations; eauto 2 with step_tactic bannot.
Qed.

Lemma are_equal_open_annot_1_rep:
  forall tvars gamma t1 t2 k rep,
    are_equal tvars gamma (open k t1 rep) t2 ->
    is_annotated_term rep ->
    is_annotated_term t1.
Proof.
  repeat step || t_annotations; eauto 2 with step_tactic bannot.
Qed.

Lemma are_equal_open_annot_2:
  forall tvars gamma t1 t2 k x,
    are_equal tvars gamma t1 (open k t2 (fvar x term_var)) ->
    is_annotated_term t2.
Proof.
  repeat step || t_annotations; eauto 2 with step_tactic bannot.
Qed.

Lemma are_equal_open2_annot_1_rep:
  forall tvars gamma t1 t2 i j rep1 rep2,
    are_equal tvars gamma (open i (open j t1 rep1) rep2) t2 ->
    is_annotated_term rep1 ->
    is_annotated_term rep2 ->
    is_annotated_term t1.
 Proof.
  repeat step || t_annotations; eauto 3 with step_tactic bannot.
Qed.

Ltac t_are_equal_open_annot_1_rep :=
  match goal with
  | H: are_equal ?tvars ?gamma (open ?k ?t1 ?rep) ?t2 |-
      is_annotated_term ?t1 =>
    apply (are_equal_open_annot_1_rep tvars gamma t1 t2 k rep H)
  end.

Hint Resolve has_type_open_annot_1: bannot.
Hint Resolve has_type_open2_annot_1: bannot.
Hint Resolve has_type_open_annot_2: bannot.
Hint Extern 50 => eapply has_type_open_annot_2_rep; eauto 1; steps: bannot.
Hint Resolve is_type_open_annot: bannot.
Hint Extern 50 => t_are_equal_open_annot_1_rep; steps; eauto 2 with bannot: bannot.
Hint Resolve are_equal_open_annot_2: bannot.
Hint Extern 50 => eapply are_equal_open2_annot_1_rep; eauto 1; steps: bannot.

Lemma has_type_topen_annot_1:
  forall tvars gamma t T k x,
    has_type tvars gamma (topen k t (fvar x type_var)) T ->
    is_annotated_term t.
Proof.
  repeat step || t_annotations; eauto 2 with step_tactic bannot.
Qed.

Lemma has_type_topen_annot_2:
  forall tvars gamma t T k x,
    has_type tvars gamma t (topen k T (fvar x type_var)) ->
    is_annotated_type T.
Proof.
  repeat step || t_annotations; eauto 2 with step_tactic bannot.
Qed.

Lemma is_type_topen_annot:
  forall tvars gamma T k X,
    is_type tvars gamma (topen k T (fvar X type_var)) ->
    is_annotated_type T.
Proof.
  repeat step || t_annotations; eauto 2 with step_tactic bannot.
Qed.

Hint Resolve has_type_topen_annot_1: bannot.
Hint Resolve has_type_topen_annot_2: bannot.
Hint Resolve is_type_topen_annot: bannot.
