Require Export SystemFR.Trees.
Require Export SystemFR.Tactics.
Require Export SystemFR.Syntax.
Require Export SystemFR.LVarOperations.
Require Export SystemFR.TypeErasure.
Require Export SystemFR.TypeErasureLemmas.

Require Import PeanoNat.

Require Import Omega.

Opaque Nat.eq_dec.

Lemma erase_term_map_indices:
  forall t i f,
    erase_term (map_indices i t f) = map_indices i (erase_term t) f.
Proof.
  induction t; steps.
Qed.

Lemma erase_type_map_indices:
  forall T i f,
    erase_type (map_indices i T f) = map_indices i (erase_type T) f.
Proof.
  induction T; repeat step || t_equality;
    eauto using erase_term_map_indices.
Qed.
