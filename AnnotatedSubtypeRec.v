Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.PolarityErase.
Require Export SystemFR.ErasedRecPos.

Opaque reducible_values.

Lemma annotated_subtype_rec:
  forall Θ Γ n1 n2 T0 Ts,
    [[ Θ; Γ ⊨ n1 ≡ n2 ]] ->
    [[ Θ; Γ ⊨ T_rec n1 T0 Ts <: T_rec n2 T0 Ts ]].
Proof.
  unfold open_subtype, open_equivalent;
    repeat step;
    eauto using reducible_values_rec_equivalent.
Qed.

Lemma annotated_subtype_rec_pos:
  forall X Θ Γ n1 n2 T0 Ts,
    wf T0 0 ->
    wf Ts 0 ->
    twf T0 0 ->
    twf Ts 1 ->
    subset (fv T0) (support Γ) ->
    subset (fv Ts) (support Γ) ->
    is_annotated_type T0 ->
    is_annotated_type Ts ->
    ~(X ∈ pfv T0 type_var) ->
    ~(X ∈ pfv Ts type_var) ->
    ~(X ∈ Θ) ->
    has_polarities (topen 0 Ts (fvar X type_var)) ((X, Positive) :: nil) ->
    [[ Θ; Γ ⊨ binary_primitive Lt n1 (succ n2) ≡ ttrue ]] ->
    [[ Θ; Γ ⊨ n1 : T_nat ]] ->
    [[ Θ; Γ ⊨ topen 0 Ts (T_rec zero T0 Ts) <: T0 ]] ->
    [[ Θ; Γ ⊨ T_rec n2 T0 Ts <: T_rec n1 T0 Ts ]].
Proof.
  unfold open_subtype, open_equivalent;
    repeat step.

  apply reducible_values_rec_pos with (psubstitute (erase_term n2) l term_var) X;
    eauto with erased;
      repeat step || side_conditions || t_instantiate_sat3 || t_pfv_in_subst || t_substitutions ||
             rewrite tlt_erase in * ||
             rewrite psubstitute_tlt in * ||
             erase_open ||
             apply_any;
      eauto using has_polarities_subst_erase;
      side_conditions;
      eauto with twf wf fv.

  - apply fv_nils2; eauto with fv.
    eapply subset_same_support; eauto; repeat step || t_subset_erase || rewrite erased_context_support.

  - apply fv_nils2; eauto with fv.
    eapply subset_same_support; eauto; repeat step || t_subset_erase || rewrite erased_context_support.
Qed.
