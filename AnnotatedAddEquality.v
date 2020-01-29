Require Export SystemFR.ErasedAddEquality.
Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.

Opaque reducible_values.

Lemma annotated_reducible_add_equality:
  forall tvars gamma e1 e2 e1' e2' x,
    ~ x ∈ pfv e1' term_var ->
    ~ x ∈ pfv e2' term_var ->
    ~ x ∈ pfv e1 term_var ->
    ~ x ∈ pfv e2 term_var ->
    ~ x ∈ pfv_context gamma term_var ->
    [[ tvars; (x, T_equiv e1' e2') :: gamma ⊨ e1 ≡ e2 ]] ->
    [[ tvars; gamma ⊨ e1' ≡ e2' ]] ->
    [[ tvars; gamma ⊨ e1 ≡ e2 ]].
Proof.
  unfold annotated_reducible;
    repeat step.

  apply open_reducible_add_equality with (erase_term e1') (erase_term e2') x;
    repeat step;
    side_conditions.
Qed.
