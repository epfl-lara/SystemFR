Require Import SystemFR.TypeErasure.
Require Import SystemFR.TypeErasureLemmas.
Require Import SystemFR.Trees.
Require Import SystemFR.Tactics.
Require Import SystemFR.NoTypeFVar.
Require Import SystemFR.Syntax.
Require Import SystemFR.Sets.

Lemma no_type_fvar_erased:
  forall T vars,
    no_type_fvar T vars ->
    no_type_fvar (erase_type T) vars.
Proof.
  unfold no_type_fvar; steps; eauto with bfv.
Qed.
