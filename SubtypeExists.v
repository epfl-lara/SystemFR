Require Export SystemFR.ErasedSingleton.

Opaque reducible_values.

Lemma sub_exists_left:
  forall ρ S T U,
    valid_interpretation ρ ->
    (forall a, [ ρ | a : S ]v -> [ ρ | open 0 T a <: U ]) ->
    [ ρ | T_exists S T <: U ].
Proof.
  unfold subtype; repeat step || simp_red; eauto.
Qed.

Lemma open_sub_exists_left_helper: forall Θ Γ S T U x,
  ~ x ∈ pfv S term_var ->
  ~ x ∈ pfv U term_var ->
  ~ x ∈ pfv T term_var ->
  ~ x ∈ pfv_context Γ term_var ->
  [ Θ; (x, S) :: Γ ⊨ open 0 T (fvar x term_var) <: U ] ->
  [ Θ; Γ ⊨ T_exists S T <: U ].
Proof.
  unfold open_subtype; repeat step || apply sub_exists_left.
  unshelve epose proof (H3 ρ ((x, a) :: l) _ _ _);
    repeat step || apply SatCons || t_substitutions;
    t_closer.
Qed.

Lemma open_sub_exists_left: forall Γ S T U x,
  ~ x ∈ pfv S term_var ->
  ~ x ∈ pfv U term_var ->
  ~ x ∈ pfv T term_var ->
  ~ x ∈ pfv_context Γ term_var ->
  [ (x, S) :: Γ ⊨ open 0 T (fvar x term_var) <: U ] ->
  [ Γ ⊨ T_exists S T <: U ].
Proof.
  eauto using open_sub_exists_left_helper.
Qed.

Lemma sub_exists_right: forall ρ S T1 T2 t U,
  valid_interpretation ρ ->
  is_erased_type T2 ->
  [ ρ | t : U ] ->
  [ ρ | T_singleton U t <: S ] ->
  (forall a, [ ρ | a : S ]v -> [ ρ | T1 <: open 0 T2 a ]) ->
  [ ρ | T1 <: T_exists S T2 ].
Proof.
  unfold subtype; repeat step || simp_red; t_closer.
  unfold reducible, reduces_to in H1; repeat step.
  exists v0; repeat step || apply_any || apply reducible_expr_value ||
               apply reducible_singleton2; t_closer;
    eauto using reducible_value_expr;
    try solve [ apply equivalent_sym; equivalent_star ].
Qed.

Opaque T_singleton.

Lemma open_sub_exists_right_helper: forall Θ Γ S T1 T2 t U x,
  ~ x ∈ pfv S term_var ->
  ~ x ∈ pfv U term_var ->
  ~ x ∈ pfv T1 term_var ->
  ~ x ∈ pfv T2 term_var ->
  ~ x ∈ pfv_context Γ term_var ->
  is_erased_type T2 ->
  [ Θ; Γ ⊨ t : U ] ->
  [ Θ; Γ ⊨ T_singleton U t <: S ] ->
  [ Θ; (x, S) :: Γ ⊨ T1 <: open 0 T2 (fvar x term_var) ] ->
  [ Θ; Γ ⊨ T1 <: T_exists S T2 ].
Proof.
  unfold open_subtype, open_reducible;
    repeat step || t_instantiate_sat3 ||
           (rewrite substitute_singleton in * by eauto with wf).

  eapply sub_exists_right; steps; eauto with erased.
  unshelve epose proof (H7 ρ ((x, a) :: l) _ _ _);
    repeat step || apply SatCons || t_substitutions; t_closer.
Qed.

Lemma open_sub_exists_right: forall Γ S T1 T2 t U x,
  ~ x ∈ pfv S term_var ->
  ~ x ∈ pfv U term_var ->
  ~ x ∈ pfv T1 term_var ->
  ~ x ∈ pfv T2 term_var ->
  ~ x ∈ pfv_context Γ term_var ->
  is_erased_type T2 ->
  [ Γ ⊨ t : U ] ->
  [ Γ ⊨ T_singleton U t <: S ] ->
  [ (x, S) :: Γ ⊨ T1 <: open 0 T2 (fvar x term_var) ] ->
  [ Γ ⊨ T1 <: T_exists S T2 ].
Proof.
  eauto using open_sub_exists_right_helper.
Qed.

Lemma sub_exists_right2: forall ρ S T1 T2 t,
  valid_interpretation ρ ->
  is_erased_type T2 ->
  [ ρ | t : S ] ->
  (forall a, [ ρ | a : S ]v -> [ ρ | T1 <: open 0 T2 a ]) ->
  [ ρ | T1 <: T_exists S T2 ].
Proof.
  unfold subtype; repeat step || simp_red; t_closer.
  unfold reducible, reduces_to in H1; repeat step.
  exists v0; repeat step || apply_any || apply reducible_expr_value ||
               apply reducible_singleton2; t_closer;
    eauto using reducible_value_expr;
    try solve [ apply equivalent_sym; equivalent_star ].
Qed.

Lemma open_sub_exists_right2_helper: forall Θ Γ S T1 T2 t x,
  ~ x ∈ pfv S term_var ->
  ~ x ∈ pfv T1 term_var ->
  ~ x ∈ pfv T2 term_var ->
  ~ x ∈ pfv_context Γ term_var ->
  is_erased_type T2 ->
  [ Θ; Γ ⊨ t : S ] ->
  [ Θ; (x, S) :: Γ ⊨ T1 <: open 0 T2 (fvar x term_var) ] ->
  [ Θ; Γ ⊨ T1 <: T_exists S T2 ].
Proof.
  unfold open_subtype, open_reducible;
    repeat step || t_instantiate_sat3 ||
           (rewrite substitute_singleton in * by eauto with wf).

  eapply sub_exists_right2; steps; eauto with erased.
  unshelve epose proof (H5 ρ ((x, a) :: l) _ _ _);
    repeat step || apply SatCons || t_substitutions; t_closer.
Qed.

Lemma open_sub_exists_right2: forall Γ S T1 T2 t x,
  ~ x ∈ pfv S term_var ->
  ~ x ∈ pfv T1 term_var ->
  ~ x ∈ pfv T2 term_var ->
  ~ x ∈ pfv_context Γ term_var ->
  is_erased_type T2 ->
  [ Γ ⊨ t : S ] ->
  [ (x, S) :: Γ ⊨ T1 <: open 0 T2 (fvar x term_var) ] ->
  [ Γ ⊨ T1 <: T_exists S T2 ].
Proof.
  eauto using open_sub_exists_right2_helper.
Qed.
