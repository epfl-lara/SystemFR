Require Export SystemFR.ReducibilitySubtype.
Require Export SystemFR.ErasedArrow.
Require Export SystemFR.RedTactics.
Require Export SystemFR.TypeSugar2.

Opaque reducible_values.

Lemma npi: forall ρ S S' T T',
  valid_interpretation ρ ->
  is_erased_type T ->
  is_erased_type T' ->
  wf T 1 ->
  wf T' 1 ->
  pfv T term_var = nil ->
  pfv T' term_var = nil ->
  [ ρ | S = S' ] ->
  (forall a, [ ρ | a : S' ]v -> [ ρ | open 0 T a = open 0 T' a ]) ->
  [ ρ | T_arrow S T = T_arrow S' T' ].
Proof.
  intros.
  unfold equivalent_types;
    repeat step || simp_red_goal || rewrite reducibility_rewrite;
    t_closer.

  - eapply equivalent_types_reducible; eauto.
    eapply reducible_app; eauto using reducible_value_expr; steps.
    eapply equivalent_types_reducible_back; eauto using reducible_value_expr.

  - eapply equivalent_types_reducible_back; eauto.
    + eapply reducible_app; eauto using reducible_value_expr; steps.
      eapply equivalent_types_reducible; eauto using reducible_value_expr.
    + apply_any; eauto using equivalent_types_reducible_values.
Qed.

Lemma open_npi_helper: forall Θ Γ S S' T T' x,
  is_erased_type T ->
  is_erased_type T' ->
  wf T 1 ->
  wf T' 1 ->
  subset (fv T) (support Γ) ->
  subset (fv T') (support Γ) ->
  ~ x ∈ pfv S' term_var ->
  ~ x ∈ pfv_context Γ term_var ->
  [ Θ; Γ ⊨ S = S' ] ->
  [ Θ; (x, S') :: Γ ⊨ open 0 T (fvar x term_var) = open 0 T' (fvar x term_var) ] ->
  [ Θ; Γ ⊨ T_arrow S T = T_arrow S' T' ].
Proof.
  unfold open_equivalent_types; repeat step || apply npi; t_closer.

  unshelve epose proof (H8 ρ ((x, a) :: l) _ _ _);
    repeat step || apply SatCons || t_substitutions; t_closer.
Qed.

Lemma open_npi: forall Γ S S' T T' x,
  is_erased_type T ->
  is_erased_type T' ->
  wf T 1 ->
  wf T' 1 ->
  subset (fv T) (support Γ) ->
  subset (fv T') (support Γ) ->
  ~ x ∈ pfv S' term_var ->
  ~ x ∈ pfv_context Γ term_var ->
  [ Γ ⊨ S = S' ] ->
  [ (x, S') :: Γ ⊨ open 0 T (fvar x term_var) = open 0 T' (fvar x term_var) ] ->
  [ Γ ⊨ T_arrow S T = T_arrow S' T' ].
Proof.
  eauto using open_npi_helper.
Qed.
