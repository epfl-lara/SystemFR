From Stdlib Require Import String.

Require Export SystemFR.ErasedSingleton.
Require Export SystemFR.SubtypeList.
Require Export SystemFR.EvalListMatch.
Require Export SystemFR.ReducibilitySubtype.
Require Export SystemFR.ErasedQuant.

Opaque reducible_values.

Opaque list_match.

Lemma reducible_union_left:
  forall ρ t T1 T2,
    valid_interpretation ρ ->
    [ ρ ⊨ t : T1 ] ->
    [ ρ ⊨ t : T_union T1 T2 ].
Proof.
  unfold reduces_to; steps.
  eexists; repeat step || simp_red; eauto using reducible_values_closed.
Qed.

Lemma reducible_union_right:
  forall ρ t T1 T2,
    valid_interpretation ρ ->
    [ ρ ⊨ t : T2 ] ->
    [ ρ ⊨ t : T_union T1 T2 ].
Proof.
  unfold reduces_to; steps.
  eexists; repeat step || simp_red; eauto using reducible_values_closed.
Qed.

Opaque List.

Lemma tmatch_value:
  forall ρ v t2 t3 T2 T3,
    valid_interpretation ρ ->
    wf t3 2 ->
    wf T2 0 ->
    wf T3 2 ->
    is_erased_term t2 ->
    is_erased_term t3 ->
    is_erased_type T2 ->
    is_erased_type T3 ->
    pfv t2 term_var = nil ->
    pfv t3 term_var = nil ->
    pfv T2 term_var = nil ->
    pfv T3 term_var = nil ->
    [ ρ ⊨ v : List ]v ->
    [ ρ ⊨ t2 : T2 ] ->
    (forall h t, [ ρ ⊨ h : T_top ] -> [ ρ ⊨ t : List ] ->
            [ ρ ⊨ open 0 (open 1 t3 h) t : open 0 (open 1 T3 h) t ]) ->
    [ ρ ⊨ list_match v t2 t3 : List_Match v T2 T3 ].
Proof.
  intros; evaluate_list_match; steps;
    eauto with wf.

  - eapply star_backstep_reducible; eauto;
      repeat step || apply wf_list_match || apply is_erased_term_list_match ||
             apply pfv_list_match;
      eauto with wf.
    unfold List_Match.
    apply reducible_union_left; auto.
    apply reducible_type_refine with uu; repeat step || simp_red || apply reducible_value_expr;
      eauto using equivalent_refl with step_tactic.

  - eapply reducibility_equivalent2; eauto using equivalent_sym;
      repeat step || list_utils; t_closer.
    unfold List_Match.
    apply reducible_union_right; auto.
    apply reducible_exists with h; repeat step || open_none; t_closer.
    + apply reducible_value_expr; repeat step || simp_red_goal.
    + apply reducible_exists with l; repeat step || open_none; t_closer;
        eauto using reducible_value_expr.
      apply reducible_type_refine with uu; repeat step || open_none; t_closer;
      eauto using reducible_value_expr.
      apply reducible_value_expr; repeat light || simp_red_goal.
      apply equivalent_refl; steps; t_closer.
Qed.

Lemma tmatch:
  forall ρ t t2 t3 T2 T3,
    valid_interpretation ρ ->
    wf t3 2 ->
    wf T2 0 ->
    wf T3 2 ->
    is_erased_term t2 ->
    is_erased_term t3 ->
    is_erased_type T2 ->
    is_erased_type T3 ->
    pfv t2 term_var = nil ->
    pfv t3 term_var = nil ->
    pfv T2 term_var = nil ->
    pfv T3 term_var = nil ->
    [ ρ ⊨ t : List ] ->
    [ ρ ⊨ t2 : T2 ] ->
    (forall h t, [ ρ ⊨ h : T_top ]v -> [ ρ ⊨ t : List ]v ->
            [ ρ ⊨ open 0 (open 1 t3 h) t : open 0 (open 1 T3 h) t ]) ->
    [ ρ ⊨ list_match t t2 t3 : List_Match t T2 T3 ].
Proof.
  intros.
  unfold reduces_to in H11; steps.
  apply reducibility_equivalent2 with (list_match v t2 t3); steps; t_closer.
  - apply equivalent_sym.
    equivalent_star;
      repeat step || apply is_erased_term_list_match || apply wf_list_match || apply pfv_list_match;
      eauto using evaluate_list_match_scrut;
      t_closer.

  - apply subtype_reducible with (List_Match v T2 T3).
    + apply tmatch_value; steps.
      unfold reduces_to in H11; steps.
      unfold reduces_to in H17; steps.
      eapply reducibility_equivalent2 with (open 0 (open 1 t3 h) v1);
        repeat step || apply is_erased_type_open || apply equivalent_context ||
               apply wf_open || apply fv_nils_open;
        t_closer;
        try solve [ apply equivalent_sym; equivalent_star ].
      eapply reducibility_rtl; steps; eauto; t_closer.
      rewrite (swap_term_holes_open t3); steps; t_closer.
      eapply reducibility_equivalent2 with (open 0 (open 1 (swap_term_holes t3 0 1) v1) v0);
        repeat step ||
               apply is_erased_type_open || apply is_erased_open ||
               apply equivalent_context || apply wf_swap_term_holes_3 ||
               apply wf_open || apply fv_nils_open;
        t_closer;
        try solve [ apply equivalent_sym; equivalent_star ].

      rewrite (swap_term_holes_open T3); steps; t_closer.
      eapply reducibility_rtl; eauto;
      repeat step || apply is_erased_type_open || apply fv_nils_open; eauto; t_closer.
      rewrite <- (swap_term_holes_open t3); steps; t_closer.
      rewrite <- (swap_term_holes_open T3); steps; t_closer.
    + apply subtype_list_match_scrut; steps.
      apply equivalent_sym; equivalent_star.
Qed.

Lemma open_tmatch_helper:
  forall Θ Γ t t2 t3 T2 T3 x1 x2,
    ~ x1 ∈ pfv_context Γ term_var ->
    ~ x2 ∈ pfv_context Γ term_var ->
    x1 <> x2 ->
    wf t3 2 ->
    wf T2 0 ->
    wf T3 2 ->
    is_erased_term t2 ->
    is_erased_term t3 ->
    is_erased_type T2 ->
    is_erased_type T3 ->
    subset (fv t2) (support Γ) ->
    subset (fv t3) (support Γ) ->
    subset (fv T2) (support Γ) ->
    subset (fv T3) (support Γ) ->
    [ Θ; Γ ⊨ t : List ] ->
    [ Θ; Γ ⊨ t2 : T2 ] ->
    [ Θ; (x1, T_top) :: (x2, List) :: Γ ⊨
        open 0 (open 1 t3 (fvar x1 term_var)) (fvar x2 term_var) :
        open 0 (open 1 T3 (fvar x1 term_var)) (fvar x2 term_var) ] ->
    [ Θ; Γ ⊨ list_match t t2 t3 : List_Match t T2 T3 ].
Proof.
  unfold open_reducible;
    repeat step || apply tmatch || t_instantiate_sat3 ||
           rewrite substitute_list_match || rewrite substitute_List_Match;
    t_closer.

  unshelve epose proof (H15 ρ ((x1, h) :: (x2, t0) :: lterms) _ _ _);
    repeat step || apply SatCons || t_substitutions;
    t_closer.
Qed.

Lemma open_tmatch:
  forall Γ t t2 t3 T2 T3 x1 x2,
    ~ x1 ∈ pfv_context Γ term_var ->
    ~ x2 ∈ pfv_context Γ term_var ->
    x1 <> x2 ->
    wf t 0 ->
    wf t2 0 ->
    wf t3 2 ->
    wf T2 0 ->
    wf T3 2 ->
    is_erased_term t ->
    is_erased_term t2 ->
    is_erased_term t3 ->
    is_erased_type T2 ->
    is_erased_type T3 ->
    subset (fv t) (support Γ) ->
    subset (fv t2) (support Γ) ->
    subset (fv t3) (support Γ) ->
    subset (fv T2) (support Γ) ->
    subset (fv T3) (support Γ) ->
    [ Γ ⊫ t : List ] ->
    [ Γ ⊫ t2 : T2 ] ->
    [ (x1, T_top) :: (x2, List) :: Γ ⊫
        open 0 (open 1 t3 (fvar x1 term_var)) (fvar x2 term_var) :
        open 0 (open 1 T3 (fvar x1 term_var)) (fvar x2 term_var) ] ->
    [ Γ ⊫ list_match t t2 t3 : T_singleton (List_Match t T2 T3) (list_match t t2 t3) ].
Proof.
  repeat step || apply open_reducible_singleton ||
         apply is_erased_term_list_match || apply wf_list_match;
    t_closer;
    eauto using open_tmatch_helper.
  eapply subset_transitive; eauto using pfv_list_match2; repeat step || sets.
Qed.
