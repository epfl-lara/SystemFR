Require Import Coq.Strings.String.

Require Export SystemFR.TypeErasure.
Require Export SystemFR.TypeErasureLemmas.
Require Export SystemFR.Syntax.
Require Export SystemFR.Trees.
Require Export SystemFR.TreeLists.
Require Export SystemFR.Tactics.

Require Export SystemFR.AssocList.

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
    try solve [ repeat step || eapply_any; eauto using annotated_term_type with exfalso ].
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

Hint Immediate annotated_open_1: bannot.
Hint Immediate annotated_open_2: bannot.

Lemma annotated_topen:
  forall t k rep,
    (is_annotated_term (topen k t rep) -> is_annotated_type rep -> is_annotated_term t) /\
    (is_annotated_type (topen k t rep) -> is_annotated_type rep -> is_annotated_type t).
Proof.
  induction t;
    try solve [ repeat step || eapply_any; eauto using annotated_term_type with exfalso ].
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

Hint Immediate annotated_topen_1: bannot.
Hint Immediate annotated_topen_2: bannot.

Lemma annotated_open_build:
  forall t k rep,
    (is_annotated_type t -> is_annotated_term rep -> is_annotated_type (open k t rep)) /\
    (is_annotated_term t -> is_annotated_term rep -> is_annotated_term (open k t rep)).
Proof.
  induction t; repeat step || eapply_any.
Qed.

Hint Extern 50 => apply annotated_open_build; steps: bannot.

Lemma annotated_topen_build:
  forall t k V,
    (is_annotated_type t -> is_annotated_type V -> is_annotated_type (topen k t V)) /\
    (is_annotated_term t -> is_annotated_type V -> is_annotated_term (topen k t V)).
Proof.
  induction t; repeat step || eapply_any.
Qed.

Hint Extern 50 => apply annotated_topen_build; steps: bannot.

Ltac t_annotated_open :=
  match goal with
  | H: is_annotated_term (open ?k ?t ?rep) |- is_annotated_term ?t =>
      poseNew (Mark 0 "once");
      apply annotated_open with k rep
  | H: is_annotated_term (open _ (open ?k ?t ?rep) _) |- is_annotated_term ?t =>
      poseNew (Mark 0 "once");
      apply annotated_open with k rep
  | H: is_annotated_type (open ?k ?t ?rep) |- is_annotated_type ?t =>
      poseNew (Mark 0 "once");
      apply annotated_open with k rep
  | H: is_annotated_term (topen ?k ?t ?rep) |- is_annotated_term ?t =>
      poseNew (Mark 0 "once");
      apply annotated_topen with k rep
  | H: is_annotated_type (topen ?k ?t ?rep) |- is_annotated_type ?t =>
      poseNew (Mark 0 "once");
      apply annotated_topen with k rep
  end.
