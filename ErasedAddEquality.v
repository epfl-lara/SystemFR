Require Export SystemFR.RedTactics.

Opaque reducible_values.

Lemma open_reducible_add_equality:
  forall tvars gamma e1 e2 e1' e2' x,
    ~ x ∈ pfv e1' term_var ->
    ~ x ∈ pfv e2' term_var ->
    ~ x ∈ pfv e1 term_var ->
    ~ x ∈ pfv e2 term_var ->
    ~ x ∈ pfv_context gamma term_var ->
    [ tvars; (x, T_equiv e1' e2') :: gamma ⊨ e1 ≡ e2 ] ->
    [ tvars; gamma ⊨ e1' ≡ e2' ] ->
    [ tvars; gamma ⊨ e1 ≡ e2 ].
Proof.
  unfold open_equivalent; steps.

  unshelve epose proof (H4 _ ((x, uu) :: l) _ _ eq_refl);
    repeat step || apply SatCons || list_utils || simp_red || t_substitutions;
    eauto.
Qed.
