Require Import Termination.TypeErasure.
Require Import Termination.TypeErasureLemmas.
Require Import Termination.Trees.
Require Import Termination.Tactics.
Require Import Termination.NoTypeFVar.
Require Import Termination.Syntax.
Require Import Termination.Sets.

Lemma no_type_fvar_erased:
  forall T vars,
    no_type_fvar T vars ->
    no_type_fvar (erase_type T) vars.
Proof.
  unfold no_type_fvar; steps; eauto with bfv.
Qed.
