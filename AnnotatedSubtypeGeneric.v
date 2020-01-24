Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.ReducibilityLemmas.

Opaque reducible_values.

Lemma annotated_subtype_generic:
  forall tvars gamma A B x,
    ~(x ∈ fv_context gamma) ->
    ~(x ∈ fv A) ->
    ~(x ∈ fv B) ->
    [[ tvars; (x, A) :: gamma ⊨ fvar x term_var : B ]] ->
    [[ tvars; gamma ⊨ A <: B ]].
Proof.
  unfold annotated_reducible, open_reducible, annotated_subtype, subtype;
    repeat step.

  unshelve epose proof (H2 theta ((x, v) :: l) _ _ _);
    repeat step || apply SatCons;
    side_conditions.

  rewrite substitute_nothing2 in *; steps; side_conditions;
    eauto using reducible_expr_value with values.
Qed.
