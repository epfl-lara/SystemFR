Require Import SystemFR.Trees.
Require Import SystemFR.Syntax.
Require Import SystemFR.Tactics.
Require Import SystemFR.AssocList.
Require Import SystemFR.TreeLists.

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
