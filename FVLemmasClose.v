Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Init.Datatypes.
Require Import Coq.Arith.PeanoNat.

Require Export SystemFR.FVLemmas.

(** Lemmas about closing locally nameless terms, unused at the moment **)

Lemma fv_close:
  forall t k x y,
    y ∈ pfv (close k t x) term_var ->
    y <> x /\ y ∈ pfv t term_var.
Proof.
  induction t;
    repeat step || list_utils || instantiate_any;
    eauto 3 using fv_close1;
    eauto with eapply_any.
Qed.

Lemma fv_tclose:
  forall t k x y,
    y ∈ pfv (tclose k t x) term_var ->
    y ∈ pfv t term_var.
Proof.
  induction t;
    repeat step || list_utils || instantiate_any;
    eauto with eapply_any.
Qed.

Lemma fv_close_same:
  forall t k x,
    x ∈ pfv (close k t x) term_var ->
    False.
Proof.
  intros; apply_anywhere fv_close; steps.
Qed.

Lemma tfv_tclose:
  forall t k x y,
    y ∈ pfv (tclose k t x) type_var ->
    y <> x /\ y ∈ pfv t type_var.
Proof.
  induction t;
    repeat step || list_utils || instantiate_any;
    eauto 3 using tfv_close1;
    eauto with eapply_any.
Qed.

Lemma tfv_close:
  forall t k x y,
    y ∈ pfv (close k t x) type_var ->
    y ∈ pfv t type_var.
Proof.
  induction t;
    repeat step || list_utils || instantiate_any;
    eauto with eapply_any.
Qed.

Lemma tfv_tclose_same:
  forall t k x,
    x ∈ pfv (tclose k t x) type_var ->
    False.
Proof.
  induction t;
    repeat step || list_utils; eauto.
Qed.

Ltac fv_close :=
  match goal with
  | H: _ ∈ pfv (close _ _ _) term_var |- _ =>
    poseNew (Mark H "fv_close");
    unshelve epose proof (fv_close _ _ _ _ H)
  | H: _ ∈ pfv (tclose _ _ _) term_var |- _ =>
    poseNew (Mark H "fv_close");
    unshelve epose proof (fv_tclose _ _ _ _ H)
  | H: _ ∈ pfv (close _ _ _) type_var |- _ =>
    poseNew (Mark H "fv_close");
    unshelve epose proof (tfv_close _ _ _ _ H)
  | H: _ ∈ pfv (tclose _ _ _) type_var |- _ =>
    poseNew (Mark H "fv_close");
    unshelve epose proof (tfv_tclose _ _ _ _ H)
  end.
