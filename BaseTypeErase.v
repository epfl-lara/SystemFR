Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import SystemFR.Trees.
Require Import SystemFR.Syntax.
Require Import SystemFR.Tactics.
Require Import SystemFR.Sets.
Require Import SystemFR.BaseType.
Require Import SystemFR.ErasedTermLemmas.
Require Import SystemFR.TypeErasure.
Require Import SystemFR.TypeErasureLemmas.

Lemma base_type_erase:
  forall X A B,
    base_type X A B ->
    base_type X (erase_type A) (erase_type B).
Proof.
  induction 1; repeat step || constructor;
    eauto with bfv;
    eauto with berased.
Qed.
