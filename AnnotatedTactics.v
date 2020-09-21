Require Export SystemFR.TypeErasureLemmas.
Require Export SystemFR.ReducibilityDefinition.
Require Export SystemFR.AnnotatedTermLemmas.

Lemma open_reducible_same:
  forall Θ Γ t T Θ' Γ' t' T',
    [ Θ; Γ ⊨ t : T ] ->
    Θ = Θ' ->
    Γ = Γ' ->
    t = t' ->
    T = T' ->
    [ Θ'; Γ' ⊨ t' : T' ].
Proof.
  steps.
Qed.

Ltac erase_open := repeat
  (progress rewrite erase_type_open in * by (steps; eauto with annot)) ||
  (progress rewrite erase_term_open in * by (steps; eauto with annot)) ||
  (progress rewrite erase_type_topen in * by (steps; eauto with annot)) ||
  (progress rewrite erase_term_topen in * by (steps; eauto with annot)).

Ltac side_conditions :=
  repeat rewrite erased_context_support in *;
  try solve [ t_subset_erase; auto ];
  eauto 2 with fv;
  eauto 2 with wf;
  eauto 2 with twf;
  eauto 2 with erased;
  try solve [ eapply_anywhere fv_context_support; eauto 2 ].
