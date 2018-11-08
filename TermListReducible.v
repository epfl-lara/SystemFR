Require Import Termination.Trees.
Require Import Termination.Syntax.
Require Import Termination.Tactics.
Require Import Termination.AssocList.
Require Import Termination.TermList.
Require Import Termination.SubstitutionErase.
Require Import Termination.TreeLists.
Require Import Termination.Sets.

Require Import Termination.ReducibilityCandidate.
Require Import Termination.ReducibilityDefinition.
Require Import Termination.ReducibilityLemmas.

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
