Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Init.Datatypes.
Require Import Coq.Arith.PeanoNat.

Require Import Termination.Syntax.
Require Import Termination.Tactics.
Require Import Termination.ListUtils.
Require Import Termination.AssocList.
Require Import Termination.Sets.
Require Import Termination.SetLemmas.
Require Import Termination.FVLemmas.

Lemma fv_close1:
  forall t k x,
    x ∈ pfv (close k t x) term_var ->
    False.
Proof.
  induction t;
    repeat step || t_listutils; eauto.
Qed.

Lemma fv_close2:
  forall t k x y,
    y ∈ pfv (close k t x) term_var ->
    y <> x /\ y ∈ pfv t term_var.
Proof.
  induction t;
    repeat match goal with
           | _ => step || t_listutils || instantiate_any
           end;
    eauto 3 using fv_close1;
    eauto 5 with beapply_any.
Qed.

Lemma fv_close3:
  forall t k x y,
    y ∈ pfv (tclose k t x) term_var ->
    y ∈ pfv t term_var.
Proof.
  induction t;
    repeat match goal with
           | _ => step || t_listutils || instantiate_any
           end;
    eauto with beapply_any.
Qed.

Lemma tfv_close1:
  forall t k x,
    x ∈ pfv (tclose k t x) type_var ->
    False.
Proof.
  induction t;
    repeat step || t_listutils; eauto.
Qed.

Lemma tfv_close2:
  forall t k x y,
    y ∈ pfv (tclose k t x) type_var ->
    y <> x /\ y ∈ pfv t type_var.
Proof.
  induction t;
    repeat match goal with
           | _ => step || t_listutils || instantiate_any
           end;
    eauto 3 using tfv_close1;
    eauto 5 with beapply_any.
Qed.

Lemma tfv_close3:
  forall t k x y,
    y ∈ pfv (close k t x) type_var ->
    y ∈ pfv t type_var.
Proof.
  induction t;
    repeat match goal with
           | _ => step || t_listutils || instantiate_any
           end;
    eauto with beapply_any.
Qed.

Ltac t_fv_close :=
  match goal with
  | H: _ ∈ pfv (close _ _ _) term_var |- _ =>
    poseNew (Mark H "t_fv_close");
    unshelve epose proof (fv_close2 _ _ _ _ H)
  | H: _ ∈ pfv (tclose _ _ _) term_var |- _ =>
    poseNew (Mark H "t_fv_close");
    unshelve epose proof (fv_close3 _ _ _ _ H)
  | H: _ ∈ pfv (tclose _ _ _) type_var |- _ =>
    poseNew (Mark H "t_fv_close");
    unshelve epose proof (tfv_close2 _ _ _ _ H)
  | H: _ ∈ pfv (tclose _ _ _) type_var |- _ =>
    poseNew (Mark H "t_fv_close");
    unshelve epose proof (tfv_close3 _ _ _ _ H)
  end.
