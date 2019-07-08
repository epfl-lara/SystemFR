Require Import SystemFR.Trees.
Require Import SystemFR.Syntax.
Require Import SystemFR.Tactics.
Require Import SystemFR.AssocList.
Require Import SystemFR.TreeLists.
Require Import SystemFR.ErasedTermLemmas.

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

Lemma subst_erased_type2:
  forall T X V,
    is_erased_type T ->
    is_erased_type V ->
    is_erased_type (psubstitute T ((X,V) :: nil) type_var).
Proof.
  induction T; repeat step || rewrite is_erased_subst;
    eauto using subst_erased.
Qed.

Hint Resolve subst_erased_type2: berased.
