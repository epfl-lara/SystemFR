Require Export SystemFR.StrictPositivity.
Require Export SystemFR.StrictPositivityLemmas.
Require Export SystemFR.Trees.
Require Export SystemFR.Syntax.
Require Export SystemFR.Tactics.
Require Export SystemFR.SizeLemmas.
Require Export SystemFR.NoTypeFVar.

Require Export SystemFR.SubstitutionLemmas.
Require Export SystemFR.ErasedTermLemmas.
Require Export SystemFR.FVLemmas.
Require Export SystemFR.FVLemmasLists.



Require Export SystemFR.AssocList.

From Stdlib Require Import List.

From Stdlib Require Import Psatz.

Opaque strictly_positive.

Lemma strictly_positive_subst_aux:
  forall n T lterms vars,
    type_nodes T < n ->
    pclosed_mapping lterms type_var ->
    twfs lterms 0 ->
    is_erased_type T ->
    strictly_positive T vars ->
    strictly_positive (psubstitute T lterms term_var) vars.
Proof.
  induction n; destruct T; repeat step || destruct_tag || simp_spos; try lia;
    eauto using no_type_fvar_subst;
    eauto with lia.
  right; exists X; steps; eauto using pfv_in_subst.
  rewrite substitute_topen2; steps.
  apply_any; repeat step || autorewrite with bsize in * || apply is_erased_type_topen;
    eauto with lia.
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
