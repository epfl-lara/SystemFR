Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import Termination.Trees.
Require Import Termination.Syntax.
Require Import Termination.Tactics.
Require Import Termination.Sets.
Require Import Termination.BaseType.
Require Import Termination.ErasedTermLemmas.
Require Import Termination.TypeErasure.
Require Import Termination.TypeErasureLemmas.

Lemma base_type_erase:
  forall X A B,
    base_type X A B ->
    base_type X (erase_type A) (erase_type B).
Proof.
  induction 1; repeat step || constructor; eauto with bfv.
Qed.
