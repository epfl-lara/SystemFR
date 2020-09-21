Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.ReducibilityLemmas.

Opaque reducible_values.

Lemma annotated_subtype_generic:
  forall Θ Γ A B x,
    ~(x ∈ fv_context Γ) ->
    ~(x ∈ fv A) ->
    ~(x ∈ fv B) ->
    [[ Θ; (x, A) :: Γ ⊨ fvar x term_var : B ]] ->
    [[ Θ; Γ ⊨ A <: B ]].
Proof.
  unfold open_reducible, open_subtype;
    repeat step.

  unshelve epose proof (H2 ρ ((x, v) :: l) _ _ _);
    repeat step || apply SatCons;
    side_conditions.

  rewrite substitute_nothing2 in *; steps; side_conditions;
    eauto using reducible_expr_value with values.
Qed.
