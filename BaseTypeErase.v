From Stdlib Require Import List.
From Stdlib Require Import String.

Require Export SystemFR.Trees.
Require Export SystemFR.Syntax.
Require Export SystemFR.Tactics.

Require Export SystemFR.BaseType.
Require Export SystemFR.ErasedTermLemmas.
Require Export SystemFR.TypeErasure.
Require Export SystemFR.TypeErasureLemmas.

Lemma base_type_erase:
  forall X A B,
    base_type X A B ->
    base_type X (erase_type A) (erase_type B).
Proof.
  induction 1; repeat step || constructor;
    eauto with fv;
    eauto with erased.
Qed.
