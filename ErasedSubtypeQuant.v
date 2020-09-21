Require Export SystemFR.ReducibilityOpenEquivalent.

Opaque reducible_values.

Lemma subtype_forall:
  forall ρ Γ t T1 T2 v l,
    valid_interpretation ρ ->
    satisfies (reducible_values ρ) Γ l ->
    [ support ρ; Γ ⊨ t : T1 ] ->
    wf T2 1 ->
    subset (fv T2) (support Γ) ->
    reducible_values ρ v (T_forall (substitute T1 l) (substitute T2 l)) ->
    reducible_values ρ v (open 0 (substitute T2 l) (substitute t l)).
Proof.
  unfold open_reducible,reduces_to;
    repeat step || t_instantiate_sat3 || simp_red || t_instantiate_reducible;
    eauto with erased wf fv.
  eapply reducibility_values_rtl; eauto;
    repeat step;
    t_closer.
Qed.

Lemma subtype_exists:
  forall ρ (Γ : context) t T1 T2 v l,
    valid_interpretation ρ ->
    satisfies (reducible_values ρ) Γ l ->
    wf T2 1 ->
    is_erased_type T2 ->
    subset (fv T2) (support Γ) ->
    [ support ρ; Γ ⊨ t : T1 ] ->
    reducible_values ρ v (open 0 (substitute T2 l) (substitute t l)) ->
    reducible_values ρ v (T_exists (substitute T1 l) (substitute T2 l)).
Proof.
  unfold open_reducible,reduces_to;
    repeat step || t_instantiate_sat3 || simp_red || t_deterministic_star;
    eauto with erased;
    t_closer.

  unshelve eexists; steps; try eassumption;
    eauto with erased wf fv.

  eapply reducibility_values_ltr; eauto;
    repeat step;
    t_closer.
Qed.
