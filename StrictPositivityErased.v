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
Require Import Termination.TypeErasure.
Require Import Termination.TypeErasureLemmas.
Require Import Termination.AnnotatedTermLemmas.

Require Import Termination.AssocList.

Require Import Coq.Lists.List.

Require Import Omega.

Opaque strictly_positive.

Lemma strictly_positive_erased_aux:
  forall n T vars,
    size T < n ->
    is_annotated_type T ->
    strictly_positive T vars ->
    strictly_positive (erase_type T) vars.
Proof.
  induction n; destruct T; repeat step || destruct_tag || simp_spos; try omega;
    eauto using no_type_fvar_erased;
    eauto with omega.
  right; exists X; steps; eauto with bfv.
  change (fvar X type_var) with (erase_type (fvar X type_var)).
  rewrite <- erase_type_topen; steps.
  apply_any;
    repeat step || autorewrite with bsize in * ||
    unshelve eauto 2 with bannot omega step_tactic.
Qed.

Lemma strictly_positive_erased:
  forall T vars,
    is_annotated_type T ->
    strictly_positive T vars ->
    strictly_positive (erase_type T) vars.
Proof.
  eauto using strictly_positive_erased_aux.
Qed.
