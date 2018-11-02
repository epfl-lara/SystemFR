Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Require Import Termination.Sets.
Require Import Termination.SetLemmas.
Require Import Termination.Typing.
Require Import Termination.AssocList.
Require Import Termination.Syntax.
Require Import Termination.Tactics.
Require Import Termination.Freshness.
Require Import Termination.ListUtils.
Require Import Termination.TermList.
Require Import Termination.SmallStep.

Require Import Termination.FVLemmas.
Require Import Termination.FVLemmasEval.
Require Import Termination.FVLemmasTyping.

Lemma context_right:
  forall gamma1 gamma2,
    is_context (gamma1 ++ gamma2) ->
    is_context gamma2.
Proof.
  induction gamma1; repeat step || step_inversion is_context.
Qed.

Ltac t_context_right :=
  match goal with
  | H: is_context (?G1 ++ ?G2) |- _ =>
    poseNew (Mark (G1,G2) "context_right");
    pose proof (context_right G1 G2 H)
  end.

Lemma is_context_fv:
  forall gamma1 gamma2 x T z,
    is_context (gamma1 ++ (x,T) :: gamma2) ->
    z ∈ fv T ->
    z ∈ support gamma2.
Proof.
  induction gamma1;
    repeat step || t_listutils || step_inversion is_context ||
           t_context_right || rewrite supportAppend in *;
    eauto using in_middle;
    eauto 3 using defined_FV_IT_1 with sets.
Qed.

Lemma is_context_fv2:
  forall gamma1 gamma2 x T z,
    is_context (gamma1 ++ (x,T) :: gamma2) ->
    z ∈ support gamma1 ->
    z ∈ fv T ->
    False.
Proof.
  induction gamma1;
    repeat step || t_listutils || step_inversion is_context || rewrite supportAppend in *;
    eauto using in_middle;
    eauto using is_context_fv.
Qed.

Ltac t_context_fv :=
  match goal with
  | H1: is_context (?G1 ++ (?x,?T) :: ?G2), H2: ?z ∈ support ?G1 |- _ =>
    poseNew (Mark (G1,G2,x,T,z) "is_context_fv2");
    pose proof (is_context_fv2 _ _ _ _ _ H1 H2)
  end.