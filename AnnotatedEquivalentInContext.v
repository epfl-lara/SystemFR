From Stdlib Require Import List.

Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.Judgments.
Require Export SystemFR.EquivalentStar.

Opaque reducible_values.

Lemma annotated_equivalent_refine_equivalent:
  forall Θ Γ Γ' x T p,
    is_annotated_term p ->
    ~ x ∈ pfv p term_var ->
    (forall z, z ∈ pfv p term_var -> z ∈ support Γ -> False) ->
    [[ Θ; Γ ++ (x, T_refine T p) :: Γ' ⊨ open 0 p (fvar x term_var) ≡ ttrue ]].
Proof.
  unfold open_equivalent;
    repeat step || satisfies_cut || rewrite erase_context_append in * || step_inversion satisfies || list_utils || simp_red.

  rewrite substitute_append2; repeat step || fv_open || t_fv_erase || list_utils || erase_open || t_substitutions;
    eauto with fv;
    try solve [ equivalent_star ].

  apply (satisfies_y_in_support _ _ _ _ _ _ x0) in H3; repeat step;
    side_conditions.
Qed.

Lemma annotated_equivalence_in_context:
  forall Θ Γ Γ' x e1 e2,
    (forall z, z ∈ pfv e1 term_var -> z ∈ support Γ -> False) ->
    (forall z, z ∈ pfv e2 term_var -> z ∈ support Γ -> False) ->
    [[ Θ; Γ ++ (x, T_equiv e1 e2) :: Γ' ⊨ e1 ≡ e2 ]].
Proof.
  unfold open_equivalent;
    repeat step || satisfies_cut || rewrite erase_context_append in * || step_inversion satisfies || list_utils || simp_red.

  rewrite substitute_append2; repeat step || fv_open || t_fv_erase || list_utils || t_substitutions.
  - rewrite substitute_append2; repeat step || fv_open || t_fv_erase || list_utils || t_substitutions.
    apply (satisfies_y_in_support _ _ _ _ _ _ x0) in H2; repeat step;
      side_conditions.
  - apply (satisfies_y_in_support _ _ _ _ _ _ x0) in H2; repeat step;
      side_conditions.
Qed.
