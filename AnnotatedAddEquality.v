Require Export SystemFR.ErasedAddEquality.
Require Export SystemFR.AnnotatedEquivalentInContext.

Opaque reducible_values.

Lemma annotated_reducible_add_equality:
  forall Θ Γ e1 e2 e1' e2' x,
    ~ x ∈ pfv e1' term_var ->
    ~ x ∈ pfv e2' term_var ->
    ~ x ∈ pfv e1 term_var ->
    ~ x ∈ pfv e2 term_var ->
    ~ x ∈ pfv_context Γ term_var ->
    [[ Θ; (x, T_equiv e1' e2') :: Γ ⊨ e1 ≡ e2 ]] ->
    [[ Θ; Γ ⊨ e1' ≡ e2' ]] ->
    [[ Θ; Γ ⊨ e1 ≡ e2 ]].
Proof.
  intros; apply open_reducible_add_equality with (erase_term e1') (erase_term e2') x;
    repeat step;
    side_conditions.
Qed.

Lemma annotated_unfold_refinement:
  forall Θ Γ Γ' e1 e2 x y T p,
    ~ y ∈ pfv p term_var ->
    ~ y ∈ pfv e1 term_var ->
    ~ y ∈ pfv e2 term_var ->
    ~ y ∈ pfv T term_var ->
    ~ y ∈ pfv_context Γ term_var ->
    ~ y ∈ pfv_context Γ' term_var ->
    ~ x ∈ pfv p term_var ->
    ~ x = y ->
    is_annotated_term p ->
    (forall z, z ∈ pfv p term_var -> z ∈ support Γ -> False) ->
    [[ Θ; (y, T_equiv (open 0 p (fvar x term_var)) ttrue) :: Γ ++ (x, T_refine T p) :: Γ' ⊨ e1 ≡ e2 ]] ->
    [[ Θ; Γ ++ (x, T_refine T p) :: Γ' ⊨ e1 ≡ e2 ]].
Proof.
  intros; apply annotated_reducible_add_equality with (open 0 p (fvar x term_var)) ttrue y;
    repeat step || fv_open || list_utils || apply annotated_equivalent_refine_equivalent;
    side_conditions.
Qed.
