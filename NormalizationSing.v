Require Export SystemFR.DeltaBetaReduction.
Require Export SystemFR.ErasedSingleton.
Require Export SystemFR.ReducibilityEquivalent.

Opaque reducible_values.

Lemma open_reduce_singleton:
  forall Θ Γ T t t',
    wf t 0 ->
    wf t' 0 ->
    [ Θ; Γ ⊨ t ≡ t' ] ->
    [ Θ; Γ ⊨ T_singleton T t = T_singleton T t' ].
Proof.
  unfold open_equivalent_types, equivalent_types;
    repeat step || simp_red || top_level_unfold open_equivalent || t_instantiate_sat3 ||
           rewrite shift_nothing2 in * by eauto with wf;
    t_closer;
    try solve [ eexists; repeat step || open_none; eauto using equivalent_trans, equivalent_sym ].
Qed.

Lemma open_nsing_helper:
  forall Θ Γ U T t t' t'',
    wf t 0 ->
    wf t' 0 ->
    wf t'' 0 ->
    wf T 0 ->
    wf U 0 ->
    is_erased_term t ->
    is_erased_term t'' ->
    is_erased_type U ->
    is_erased_type T ->
    subset (fv U) (support Γ) ->
    subset (fv T) (support Γ) ->
    [ Θ; Γ ⊨ t ≡ t' ] ->
    [ Θ; Γ ⊨ t : U ] ->
    [ Θ; Γ ⊨ t' : T_singleton T t'' ] ->
    [ Θ; Γ ⊨ T_singleton U t = T_singleton T t'' ].
Proof.
  unfold T_singleton;
    repeat step || unfold open_equivalent_types || unfold equivalent_types || simp_red ||
           open_none || unfold open_equivalent in * ||
           unfold open_reducible in * || t_instantiate_sat3 ||
           (rewrite shift_nothing2 in * by eauto with wf);
    t_closer.

  - apply reducible_expr_value; eauto with values.
    eapply reducibility_equivalent2; eauto using equivalent_sym; steps; t_closer.
    apply reducibility_equivalent2 with (psubstitute t' l term_var); steps;
      eauto using equivalent_sym;
      eauto using reducible_type_refine2;
      t_closer.

  - eexists; steps.
    unfold reducible, reduces_to in H22; repeat step || simp_red || open_none.
    eapply equivalent_trans; eauto.
    eapply equivalent_trans; eauto.
    eapply equivalent_trans; eauto; equivalent_star.

  - apply reducible_expr_value; eauto with values.
    eapply reducibility_equivalent2; eauto using equivalent_sym; steps; t_closer.

    unfold reducible, reduces_to in H22; repeat step || simp_red || open_none.
    eapply reducibility_equivalent2; eauto; steps; t_closer.
    eapply reducibility_equivalent2; eauto; steps; t_closer.
    eapply equivalent_trans; eauto; equivalent_star.

  - eexists; steps.
    unfold reducible, reduces_to in H22; repeat step || simp_red || open_none.
    eapply equivalent_trans; eauto.
    eapply equivalent_trans; eauto using equivalent_sym.
    apply equivalent_trans with (psubstitute t' l term_var);
      try solve [ apply equivalent_sym; equivalent_star ];
      eauto using equivalent_sym.
Qed.

Lemma open_nsing:
  forall Γ U T t t' t'',
    wf t 0 ->
    wf t' 0 ->
    wf t'' 0 ->
    wf T 0 ->
    wf U 0 ->
    is_erased_term t ->
    is_erased_term t'' ->
    is_erased_type U ->
    is_erased_type T ->
    subset (fv U) (support Γ) ->
    subset (fv T) (support Γ) ->
    [ Γ ⊨ t ⤳* t' ] ->
    [ Γ ⊨ t : U ] ->
    [ Γ ⊨ t' : T_singleton T t'' ] ->
    [ Γ ⊨ T_singleton U t = T_singleton T t'' ].
Proof.
  eauto using open_nsing_helper, delta_beta_obs_equiv.
Qed.
