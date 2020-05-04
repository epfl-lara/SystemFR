Require Export SystemFR.ReducibilitySubtype.
Require Export SystemFR.ReducibilityLemmas.
Require Export SystemFR.TermListReducible.
Require Export SystemFR.SubstitutionErase.
Require Export SystemFR.ScalaDepSugar.

Opaque reducible_values.

Lemma nexists_1: forall ρ s S S' T T',
  valid_interpretation ρ ->
  is_erased_type T ->
  is_erased_type T' ->
  wf T 1 ->
  wf T' 0 ->
  pfv T term_var = nil ->
  pfv T' term_var = nil ->
  [ ρ | s : S ] ->
  [ ρ | S = S' ] ->
  (forall a, [ ρ | a : S' ]v -> [ ρ | open 0 T a = T' ]) ->
  [ ρ | T_exists S T = T' ].
Proof.
  intros; unfold equivalent_types;
    repeat step || simp_red || rewrite reducibility_rewrite;
    t_closer;
    eauto using equivalent_types_reducible_values.

 unfold reducible, reduces_to in H6; steps.
 exists v0; steps; eauto with wf fv erased;
   eauto using equivalent_types_reducible_values, equivalent_types_reducible_values_back.
Qed.

Lemma open_nexists_1_helper: forall Θ Γ s S S' T T' x,
  is_erased_type T ->
  is_erased_type T' ->
  wf T 1 ->
  wf T' 0 ->
  subset (fv T) (support Γ) ->
  subset (fv T') (support Γ) ->
  ~ x ∈ pfv S' term_var ->
  ~ x ∈ pfv T' term_var ->
  ~ x ∈ pfv_context Γ term_var ->
  [ Θ; Γ ⊨ s : S ] ->
  [ Θ; Γ ⊨ S = S' ] ->
  [ Θ; (x, S') :: Γ ⊨ open 0 T (fvar x term_var) = T' ] ->
  [ Θ; Γ ⊨ T_exists S T = T' ].
Proof.
  unfold open_reducible, open_equivalent_types; repeat step || eapply nexists_1; t_closer.

  unshelve epose proof (H10 ρ ((x, a) :: l) _ _ _);
    repeat step || apply SatCons || t_substitutions; t_closer.
Qed.

Lemma open_nexists_1: forall Γ s S S' T T' x,
  is_erased_type T ->
  is_erased_type T' ->
  wf T 1 ->
  wf T' 0 ->
  subset (fv T) (support Γ) ->
  subset (fv T') (support Γ) ->
  ~ x ∈ pfv S' term_var ->
  ~ x ∈ pfv T' term_var ->
  ~ x ∈ pfv_context Γ term_var ->
  [ Γ ⊨ s : S ] -> (* algorithm invariant: every type is inhabited *)
  [ Γ ⊨ S = S' ] ->
  [ (x, S') :: Γ ⊨ open 0 T (fvar x term_var) = T' ] ->
  [ Γ ⊨ T_exists S T = T' ].
Proof.
  eauto using open_nexists_1_helper.
Qed.

Lemma nexists_2: forall ρ S S' T T',
  valid_interpretation ρ ->
  is_erased_type T ->
  is_erased_type T' ->
  wf T 1 ->
  wf T' 1 ->
  pfv T term_var = nil ->
  pfv T' term_var = nil ->
  [ ρ | S = S' ] ->
  (forall a, [ ρ | a : S' ]v -> [ ρ | open 0 T a = open 0 T' a ]) ->
  [ ρ | T_exists S T = T_exists S' T' ].
Proof.
  intros; unfold equivalent_types;
    repeat step || simp_red || rewrite reducibility_rewrite;
    t_closer.

  - exists a; steps; eauto using equivalent_types_reducible_values.
  - exists a; steps; eauto using equivalent_types_reducible_values_back.
Qed.

Lemma open_nexists_2_helper: forall Θ Γ S S' T T' x,
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
  [ Θ; Γ ⊨ T_exists S T = T_exists S' T' ].
Proof.
  unfold open_equivalent_types; repeat step || apply nexists_2; t_closer.

  unshelve epose proof (H8 ρ ((x, a) :: l) _ _ _);
    repeat step || apply SatCons || t_substitutions; t_closer.
Qed.

Lemma open_nexists_2: forall Γ S S' T T' x,
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
  [ Γ ⊨ T_exists S T = T_exists S' T' ].
Proof.
  eauto using open_nexists_2_helper.
Qed.
