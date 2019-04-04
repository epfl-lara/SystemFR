Require Import SystemFR.Trees.
Require Import SystemFR.Syntax.
Require Import SystemFR.Tactics.
Require Import SystemFR.AssocList.
Require Import SystemFR.TermList.
Require Import SystemFR.SubstitutionErase.
Require Import SystemFR.TreeLists.
Require Import SystemFR.Sets.

Require Import SystemFR.ReducibilityCandidate.
Require Import SystemFR.ReducibilityDefinition.
Require Import SystemFR.ReducibilityLemmas.

Require Import PeanoNat.

Open Scope list_scope.

Opaque reducible_values.

Lemma satisfies_erased_terms:
  forall theta l gamma,
    valid_interpretation theta ->
    satisfies (reducible_values theta) gamma l ->
    erased_terms l.
Proof.
  induction l; repeat step || step_inversion satisfies;
    eauto with berased.
Qed.

Hint Resolve satisfies_erased_terms: berased.
