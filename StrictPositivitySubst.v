Require Import Termination.StrictPositivity.
Require Import Termination.StrictPositivityLemmas.
Require Import Termination.Trees.
Require Import Termination.Syntax.
Require Import Termination.Tactics.
Require Import Termination.SizeLemmas.
Require Import Termination.NoTypeFVar.
Require Import Termination.Sets.
Require Import Termination.SubstitutionLemmas.
Require Import Termination.ErasedTermLemmas.
Require Import Termination.FVLemmas.
Require Import Termination.FVLemmasLists.

Require Import Termination.WellFormed.

Require Import Termination.AssocList.

Require Import Coq.Lists.List.

Require Import Omega.

Opaque strictly_positive.

Lemma strictly_positive_subst_aux:
  forall n T lterms vars,
    size T < n ->
    pclosed_mapping lterms type_var ->
    twfs lterms 0 ->
    is_erased_type T ->
    strictly_positive T vars ->
    strictly_positive (psubstitute T lterms term_var) vars.
Proof.
  induction n; destruct T; repeat step || destruct_tag || simp_spos; try omega;
    eauto using no_type_fvar_subst;
    eauto with omega.
  right; exists X; steps; eauto using pfv_in_subst.
  rewrite substitute_topen2; steps.
  apply_any; repeat step || autorewrite with bsize in * || apply is_erased_type_topen;
    eauto with omega.
Qed.

Lemma strictly_positive_subst:
  forall T lterms vars,
    pclosed_mapping lterms type_var ->
    twfs lterms 0 ->
    is_erased_type T ->
    strictly_positive T vars ->
    strictly_positive (psubstitute T lterms term_var) vars.
Proof.
  eauto using strictly_positive_subst_aux.
Qed.
