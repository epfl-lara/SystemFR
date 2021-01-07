Require Import PeanoNat.

Require Export SystemFR.NormalizationSing.
Require Export SystemFR.SubtypeList.
Require Export SystemFR.InferMatch.
Require Export SystemFR.CloseLemmas.

Opaque reducible_values.

Lemma open_nmatch_3: forall Γ T2 T3 t t',
  is_erased_type T2 ->
  is_erased_type T3 ->
  wf T2 0 ->
  wf T3 2 ->
  subset (fv T2) (support Γ) ->
  subset (fv T3) (support Γ) ->
  [ Γ ⊨ t ⤳* t' ] ->
  [ Γ ⊫ List_Match t T2 T3 = List_Match t' T2 T3 ].
Proof.
  eauto using open_sub_list_match_scrut, delta_beta_obs_equiv.
Qed.

Lemma nmatch_nil: forall ρ T2 T3,
  valid_interpretation ρ ->
  [ ρ ⊨ List_Match tnil T2 T3 = T2 ].
Proof.
  unfold equivalent_types, List_Match;
    repeat step || simp_red_top_level_goal || simp_red_top_level_hyp || open_none;
    eauto using reducible_values_closed.

  - apply_anywhere equivalent_value_left; steps; eauto with closing values.
  - left; repeat step || simp_red || exists uu;
      eauto using reducible_values_closed;
      eauto using equivalent_refl.
Qed.

Lemma reducibility_open_equivalent2:
  forall T t1 t2 t1' t2' ρ v,
    [ ρ ⊨ v : open 0 (open 1 T t1) t2 ]v  ->
    valid_interpretation ρ ->
    is_erased_type T ->
    wf T 2 ->
    pfv T term_var = nil ->
    [ t1 ≡ t1' ] ->
    [ t2 ≡ t2' ] ->
    [ ρ ⊨ v : open 0 (open 1 T t1') t2' ]v.
Proof.
  intros.
  eapply reducibility_open_equivalent; eauto; steps; eauto with erased wf fv.
  rewrite swap_term_holes_open in * by (
    unfold equivalent_terms; repeat step || destruct_and; t_closer
  ).
  eapply reducibility_open_equivalent; eauto; steps; eauto with erased wf fv.
Qed.

Opaque List.

Lemma nmatch_cons: forall ρ t ts T2 T3,
  valid_interpretation ρ ->
  wf t 0 ->
  wf ts 0 ->
  is_erased_term t ->
  is_erased_term ts ->
  pfv t term_var = nil ->
  pfv ts term_var = nil ->
  wf T3 2 ->
  pfv T3 term_var = nil ->
  is_erased_type T3 ->
  [ ρ ⊨ t : T_top ] ->
  [ ρ ⊨ ts : List ] ->
  [ ρ ⊨ List_Match (tcons t ts) T2 T3 = open 0 (open 1 T3 t) ts ].
Proof.
  unfold equivalent_types, List_Match;
    repeat step || simp_red_top_level_goal || simp_red_top_level_hyp || open_none;
    eauto using reducible_values_closed;
    eauto 3 using right_left_equivalence with exfalso values.

  - apply_anywhere tright_equiv; eauto with closing values.
    eapply reducibility_open_equivalent2; try eassumption; steps;
      eauto 3 using equivalent_sym, pair_equiv_1, pair_equiv_2 with closing.

  - right; repeat step.
    apply reducible_expr_value; eauto with values.
    apply reducible_exists with t;
      repeat step || list_utils || rewrite open_list || open_none; eauto with fv wf erased.
    apply reducible_exists with ts;
      repeat step || list_utils || open_none; eauto with fv wf erased.
    apply reducible_type_refine with uu; repeat step || open_none || list_utils;
      eauto with fv wf erased;
      eauto using reducible_value_expr.
    apply reducible_value_expr; repeat step || simp_red_goal.
    apply equivalent_refl; repeat step || list_utils.
Qed.

Opaque List_Match.

Lemma open_nmatch_nil: forall Θ Γ T2 T3,
  [ Θ; Γ ⊨ List_Match tnil T2 T3 = T2 ].
Proof.
  unfold open_equivalent_types; repeat step || rewrite substitute_List_Match;
    eauto with wf;
    eauto using nmatch_nil.
Qed.

Lemma open_nmatch_1: forall Γ T2 T2' T3 t,
  is_erased_type T2 ->
  is_erased_type T3 ->
  wf T2 0 ->
  wf T3 2 ->
  subset (fv T2) (support Γ) ->
  subset (fv T3) (support Γ) ->
  [ Γ ⊨ t ⤳* tnil ] ->
  [ Γ ⊫ T2 = T2' ] ->
  [ Γ ⊫ List_Match t T2 T3 = T2' ].
Proof.
  intros.
  eapply open_equivalent_types_trans; try apply open_nmatch_3;
    eauto using open_equivalent_types_trans, open_nmatch_nil.
Qed.

Lemma open_nmatch_cons: forall Θ Γ T2 T3 t1 t2,
  wf t1 0 ->
  wf t2 0 ->
  wf T3 2 ->
  is_erased_term t1 ->
  is_erased_term t2 ->
  is_erased_type T3 ->
  subset (fv t1) (support Γ) ->
  subset (fv t2) (support Γ) ->
  subset (fv T3) (support Γ) ->
  [ Θ; Γ ⊨ t1 : T_top ] ->
  [ Θ; Γ ⊨ t2 : List ] ->
  [ Θ; Γ ⊨ List_Match (tcons t1 t2) T2 T3 = open 0 (open 1 T3 t1) t2 ].
Proof.
  unfold open_equivalent_types, open_reducible;
    repeat step || rewrite substitute_List_Match || t_substitutions ||
           t_instantiate_sat3 || apply nmatch_cons;
    eauto with wf erased fv.
Qed.

Lemma reducibility_subst_equiv:
  forall ρ v T x t1 t2,
    [ ρ ⊨ v : psubstitute T ((x, t1) :: nil) term_var ]v ->
    valid_interpretation ρ ->
    wf T 0 ->
    is_erased_type T ->
    subset (fv T) (x :: nil) ->
    [ t1 ≡ t2 ] ->
    [ ρ ⊨ v : psubstitute T ((x, t2) :: nil) term_var ]v.
Proof.
  intros; repeat rewrite <- (open_close _ _ _ 0) in * by auto.
  rewrite <- (open_close _ _ _ 0) in H by auto.
  eapply reducibility_open_equivalent; eauto; repeat step;
    eauto with erased wf;
    eauto using fv_close_nil2.
Qed.

Lemma reducibility_subst_equiv2:
  forall ρ T x t1 t2,
    valid_interpretation ρ ->
    wf T 0 ->
    is_erased_type T ->
    subset (fv T) (x :: nil) ->
    [ t1 ≡ t2 ] ->
    [ ρ ⊨ psubstitute T ((x, t1) :: nil) term_var = psubstitute T ((x, t2) :: nil) term_var ].
Proof.
  unfold equivalent_types; steps;
    eauto using reducibility_subst_equiv, equivalent_sym.
Qed.

Lemma subset_diff:
  forall s1 x s2,
    subset s1 (x :: s2) ->
    subset (s1 -- (x :: nil)) s2.
Proof.
  unfold subset; repeat step || instantiate_any || rewrite in_remove in *.
Qed.

Opaque diff.

Lemma subset_diff2:
  forall s1 x s2,
    subset s1 (x :: s2) ->
    subset (s1 -- s2) (x :: nil).
Proof.
  unfold subset; repeat step || instantiate_any || rewrite in_diff in *.
Qed.

Lemma closed_mapping_fv2:
  forall l tag,
    pclosed_mapping l tag ->
    pfv_range l tag = nil.
Proof.
  induction l; repeat step || list_utils.
Qed.

Lemma reducibility_subst_equiv3:
  forall ρ T x l t1 t2,
    valid_interpretation ρ ->
    wf T 0 ->
    is_erased_type T ->
    ~ x ∈ support l ->
    wfs l 0 ->
    erased_terms l ->
    pclosed_mapping l term_var ->
    subset (fv T) (x :: support l) ->
    [ t1 ≡ t2 ] ->
    [ ρ ⊨ psubstitute T ((x, t1) :: l) term_var = psubstitute T ((x, t2) :: l) term_var ].
Proof.
  intros.
  repeat rewrite (substitute_cons4 _ T); steps.
  apply reducibility_subst_equiv2; steps; eauto with wf erased fv.
  eapply subset_transitive; eauto using fv_subst2;
    repeat step || sets || rewrite closed_mapping_fv2 by auto;
    eauto using subset_diff2;
    eauto with sets.
Qed.

Lemma in_support_in_context:
  forall P Γ l x,
    x ∈ support l ->
    satisfies P Γ l ->
    x ∈ pfv_context Γ term_var.
Proof.
  intros; apply fv_context_support; erewrite satisfies_same_support; eauto.
Qed.

Lemma open_instantiate:
  forall Θ Γ x t T T1 T2,
    ~ x ∈ fv T ->
    ~ x ∈ fv_context Γ ->
    wf T1 0 ->
    wf T2 0 ->
    is_erased_type T1 ->
    is_erased_type T2 ->
    subset (fv T1) (x :: support Γ) ->
    subset (fv T2) (x :: support Γ) ->
    [ Θ; Γ ⊨ t : T ] ->
    [ Θ; (x, T) :: Γ ⊨ T1 = T2 ] ->
    [ Θ; Γ ⊨ psubstitute T1 ((x, t) :: nil) term_var = psubstitute T2 ((x, t) :: nil) term_var ].
Proof.
  unfold open_equivalent_types, open_reducible; repeat step || t_instantiate_sat3.
  top_level_unfold reduces_to; steps.
  unshelve epose proof (H8 ρ ((x, v) :: l) _ _);
    repeat step || apply SatCons || (rewrite <- substitute_cons3 by steps);
    eauto with fv wf twf erased.

  eapply equivalent_types_trans; try eapply reducibility_subst_equiv3;
    repeat step || erewrite satisfies_same_support in * by eauto;
    try solve [ equivalent_star ];
    eauto using in_support_in_context;
    eauto with wf erased fv.

  eapply equivalent_types_trans; eauto; apply equivalent_types_sym.

  apply reducibility_subst_equiv3;
    repeat step || erewrite satisfies_same_support in * by eauto;
    try solve [ equivalent_star ];
    eauto using in_support_in_context;
    eauto with wf erased fv.
Qed.

Lemma open_reducible_weaken:
  forall Θ Γ x A t B,
    ~ x ∈ fv t ->
    ~ x ∈ fv B ->
    [ Θ; Γ ⊨ t : B ] ->
    [ Θ; (x, A) :: Γ ⊨ t : B ].
Proof.
  unfold open_reducible; repeat step || step_inversion satisfies || t_substitutions.
Qed.

Lemma open_nmatch_2: forall Γ T2 T3 T3' t t1 t2 x y,
  is_erased_term t1 ->
  is_erased_term t2 ->
  is_erased_type T2 ->
  is_erased_type T3 ->
  is_erased_type T3' ->
  wf t1 0 ->
  wf t2 0 ->
  wf T2 0 ->
  wf T3 2 ->
  wf T3' 0 ->
  subset (fv t1) (support Γ) ->
  subset (fv t2) (support Γ) ->
  subset (fv T2) (support Γ) ->
  subset (fv T3) (support Γ) ->
  subset (fv T3') (support Γ) ->
  ~ x ∈ fv t1 ->
  ~ x ∈ fv t2 ->
  ~ x ∈ fv T3 ->
  ~ x ∈ fv T3' ->
  ~ x ∈ fv_context Γ ->
  ~ y ∈ fv t1 ->
  ~ y ∈ fv t2 ->
  ~ y ∈ fv T3 ->
  ~ y ∈ fv T3' ->
  ~ y ∈ fv_context Γ ->
  x <> y ->
  [ Γ ⊫ t1 : T_top ] ->
  [ Γ ⊫ t2 : List ] ->
  [ Γ ⊨ t ⤳* tcons t1 t2 ] ->
  [ (x, T_singleton T_top t1) :: (y, T_singleton List t2) :: Γ ⊫
    open 0 (open 1 T3 (fvar x term_var)) (fvar y term_var) = T3' ] ->
  [ Γ ⊫ List_Match t T2 T3 = T3' ].
Proof.
  intros.
  eapply open_equivalent_types_trans; try apply open_nmatch_3; try eassumption; steps.
  eapply open_equivalent_types_trans; try apply open_nmatch_cons; steps.
  apply (open_instantiate _ _ _ t1) in H28;
    repeat step || list_utils || apply wf_open || apply is_erased_type_open ||
           rewrite pfv_shift2 in *;
    eauto with fv wf erased;
    eauto using subset_add2.
  - apply (open_instantiate _ _ _ t2) in H28;
      repeat step || list_utils || apply wf_open || apply wf_subst || t_substitutions ||
             apply is_erased_type_open || apply subst_erased_type ||
             rewrite pfv_shift2 in *;
      eauto with fv wf erased;
      eauto using subset_add2;
      eauto using open_reducible_singleton.

    + rewrite (substitute_nothing2 T3') in *; repeat step || rewrite substitute_nothing3 in *.
      rewrite (substitute_nothing2 T3') in *; repeat step || rewrite substitute_nothing3 in *.

    + eapply subset_transitive; eauto using fv_open; repeat step || sets.
      eapply subset_transitive; eauto using fv_open; repeat step || sets;
        eauto using subset_add2.

  - eapply subset_transitive; eauto using fv_open; repeat step || sets.
    eapply subset_transitive; eauto using fv_open; repeat step || sets;
      eauto using subset_add2.
  - apply open_reducible_weaken; repeat step || rewrite pfv_shift2 in *;
      eauto using open_reducible_singleton.
Qed.
