Require Import Termination.Trees.
Require Import Termination.Syntax.
Require Import Termination.Tactics.
Require Import Termination.AssocList.
Require Import Termination.TreeLists.
Require Import Termination.TypeErasure.

Require Import PeanoNat.

Open Scope list_scope.

Lemma subst_erased:
  forall t l tag,
    is_erased_term t ->
    erased_terms l ->
    is_erased_term (psubstitute t l tag).
Proof.
  induction t; steps; eauto using erased_term_in_list.
Qed.

Hint Resolve subst_erased: berased.

Lemma subst_erased_type:
  forall t l,
    is_erased_type t ->
    erased_terms l ->
    is_erased_type (psubstitute t l term_var).
Proof.
  induction t; steps;
    eauto using subst_erased;
    eauto using erased_term_in_list.
Qed.

Hint Resolve subst_erased_type: berased.

(*
Lemma subst_erase:
  forall t l tag,
    erased_terms l ->
    psubstitute (erase_term t) l tag = erase_term (psubstitute t l tag).
Proof.
  induction t;
    try solve [ steps ].
  - steps.
*)
