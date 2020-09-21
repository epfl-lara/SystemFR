Require Export SystemFR.ErasedLet.
Require Export SystemFR.ReducibilityOpenEquivalent.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducible_forall:
  forall ρ t U V A,
    valid_interpretation ρ ->
    [ ρ ⊨ t : A ] ->
    wf U 0 ->
    fv U = nil ->
    is_erased_type V ->
    (forall u, [ ρ ⊨ u : U ]v -> [ ρ ⊨ t : open 0 V u ]) ->
    [ ρ ⊨ t : T_forall U V ].
Proof.
  unfold reduces_to;
  repeat step || list_utils || unfold reduces_to || simp_red ||
         rewrite reducibility_rewrite;
    eauto 2 with cbvlemmas;
    eauto with fv wf;
    eauto using red_is_val.

  exists v; repeat step || simp_red || t_deterministic_star || instantiate_any;
    t_closer.
Qed.

Lemma open_reducible_forall:
  forall Θ Γ x t U V A,
    ~(x ∈ fv t) ->
    ~(x ∈ fv U) ->
    ~(x ∈ fv V) ->
    ~(x ∈ fv_context Γ) ->
    wf U 0 ->
    subset (fv U) (support Γ) ->
    subset (fv t) (support Γ) ->
    is_erased_type V ->
    [ Θ; Γ ⊨ t : A ] ->
    [ Θ; (x, U) :: Γ ⊨ t : open 0 V (fvar x term_var) ] ->
    [ Θ; Γ ⊨ t : T_forall U V ].
Proof.
  unfold open_reducible in *; repeat step || t_instantiate_sat3.

  eapply reducible_forall; steps; t_closer.
  unshelve epose proof (H8 ρ ((x,u) :: lterms) _ _ _);
    repeat step || list_utils || apply SatCons || t_substitutions;
    t_closer;
    eauto with twf.
Qed.

Lemma open_reducible_exists_elim:
  forall Θ (Γ : context) p U V t T u v,
    ~(u ∈ fv_context Γ) ->
    ~(u ∈ fv t) ->
    ~(u ∈ fv U) ->
    ~(u ∈ fv V) ->
    ~(u ∈ fv T) ->
    ~(v ∈ fv_context Γ) ->
    ~(u ∈ fv t) ->
    ~(v ∈ fv U) ->
    ~(v ∈ fv V) ->
    ~(v ∈ fv T) ->
    ~(u = v) ->
    wf U 0 ->
    wf V 1 ->
    wf t 1 ->
    wf T 0 ->
    is_erased_type T ->
    is_erased_term t ->
    subset (fv U) (support Γ) ->
    subset (fv V) (support Γ) ->
    subset (fv T) (support Γ) ->
    subset (fv t) (support Γ) ->
    [ Θ; Γ ⊨ p : T_exists U V ] ->
    [ Θ; (v, open 0 V (fvar u term_var)) :: (u, U) :: Γ ⊨
        open 0 t (fvar v term_var) : T ] ->
    [ Θ; Γ ⊨ app (notype_lambda t) p : T ].
Proof.
  unfold open_reducible; repeat step || t_instantiate_sat3.
  pose proof H5 as Copy.
  unfold reduces_to in H5.
  repeat step || t_instantiate_sat3 || list_utils || simp_red || t_deterministic_star ||
         apply reducible_let2 with
             (T_exists (psubstitute U lterms term_var) (psubstitute V lterms term_var)); t_closer.

  unshelve epose proof (H21 ρ ((v, v1) :: (u,a) :: lterms) _ _ _);
    repeat step || list_utils || apply SatCons || t_substitutions || fv_open;
    t_closer;
    eauto with twf.
Qed.

Lemma open_reducible_forall_inst:
  forall (Θ : list nat) (Γ : context) (t1 t2 U V : tree),
    is_erased_term t1 ->
    is_erased_term t2 ->
    wf t1 0 ->
    wf t2 0 ->
    wf V 1 ->
    subset (fv t1) (support Γ) ->
    subset (fv t2) (support Γ) ->
    subset (fv V) (support Γ) ->
    [ Θ; Γ ⊨ t1 : T_forall U V ] ->
    [ Θ; Γ ⊨ t2 : U ] ->
    [ Θ; Γ ⊨ t1 : open 0 V t2 ].
Proof.
  repeat step || unfold open_reducible,reduces_to in * || simp_red ||
         t_instantiate_sat3 || find_smallstep_value;
    try t_closing;
    eauto with fv wf.

  rewrite substitute_open; eauto with wf.
  eapply reducibility_values_rtl; try eassumption; steps;
    eauto with wf fv erased.
Qed.
