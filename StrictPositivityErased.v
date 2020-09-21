Require Export SystemFR.StrictPositivity.
Require Export SystemFR.StrictPositivityLemmas.
Require Export SystemFR.Trees.
Require Export SystemFR.Syntax.
Require Export SystemFR.Tactics.
Require Export SystemFR.SizeLemmas.
Require Export SystemFR.NoTypeFVar.

Require Export SystemFR.SubstitutionLemmas.
Require Export SystemFR.ErasedTermLemmas.
Require Export SystemFR.TypeErasure.
Require Export SystemFR.TypeErasureLemmas.
Require Export SystemFR.AnnotatedTermLemmas.
Require Export SystemFR.NoTypeFVarErased.

Require Export SystemFR.AssocList.

Require Import Coq.Lists.List.

Require Import Psatz.

Opaque strictly_positive.

Lemma strictly_positive_erased_aux:
  forall n T vars,
    type_nodes T < n ->
    is_annotated_type T ->
    strictly_positive T vars ->
    strictly_positive (erase_type T) vars.
Proof.
  induction n; destruct T; repeat step || destruct_tag || simp_spos; try lia;
    eauto using no_type_fvar_erased;
    eauto with lia.
  right; exists X; steps; eauto with fv.
  change (fvar X type_var) with (erase_type (fvar X type_var)).
  rewrite <- erase_type_topen; steps.
  apply_any;
    repeat step || autorewrite with bsize in * ||
    unshelve eauto 2 with annot lia step_tactic.
Qed.

Lemma strictly_positive_erased:
  forall T vars,
    is_annotated_type T ->
    strictly_positive T vars ->
    strictly_positive (erase_type T) vars.
Proof.
  eauto using strictly_positive_erased_aux.
Qed.
