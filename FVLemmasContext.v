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
Require Import Termination.SmallStep.
Require Import Termination.TermList.

Require Import Termination.FVLemmas.
Require Import Termination.FVLemmasEval.
Require Import Termination.FVLemmasTyping.

Lemma context_right:
  forall tvars gamma1 gamma2,
    is_context tvars (gamma1 ++ gamma2) ->
    is_context tvars gamma2.
Proof.
  induction gamma1; repeat step || step_inversion is_context.
Qed.

Ltac t_context_right :=
  match goal with
  | H: is_context ?tvars (?G1 ++ ?G2) |- _ =>
    poseNew (Mark (tvars,G1,G2) "context_right");
    pose proof (context_right tvars G1 G2 H)
  end.

Lemma is_context_fv:
  forall tvars gamma1 gamma2 x T z,
    is_context tvars (gamma1 ++ (x,T) :: gamma2) ->
    z ∈ pfv T term_var ->
    z ∈ support gamma2.
Proof.
  induction gamma1;
    repeat step || step_inversion is_context || p_fv;
      eauto with step_tactic.
Qed.

Lemma is_context_fv2:
  forall tvars gamma1 gamma2 x T z,
    is_context tvars (gamma1 ++ (x,T) :: gamma2) ->
    z ∈ support gamma1 ->
    z ∈ pfv T term_var ->
    False.
Proof.
  induction gamma1 as [ | g gs ];
    repeat step || step_inversion is_context || rewrite supportAppend in * || t_listutils; eauto.
  epose proof (is_context_fv _ _ _ _ _ _ H4 H1); repeat steps || t_listutils.
Qed.

Ltac t_context_fv :=
  match goal with
  | H1: is_context ?tvars (?G1 ++ (?x,?T) :: ?G2), H2: ?z ∈ support ?G1 |- _ =>
    poseNew (Mark (tvars,G1,G2,x,T,z) "is_context_fv2");
    pose proof (is_context_fv2 _ _ _ _ _ _ H1 H2)
  end.
