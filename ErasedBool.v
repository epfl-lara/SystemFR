From Equations Require Import Equations.
From Stdlib Require Import List.

Require Export SystemFR.RedTactics.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducible_true:
  forall ρ, [ ρ ⊨ ttrue : T_bool ]v.
Proof.
  repeat step || simp_red.
Qed.

Lemma open_reducible_true:
  forall Θ Γ,
    [ Θ; Γ ⊨ ttrue : T_bool ].
Proof.
  unfold open_reducible,reduces_to, closed_term in *; steps;
    eauto using reducible_true with star.
Qed.

Lemma reducible_false:
  forall ρ, [ ρ ⊨ tfalse : T_bool ]v.
Proof.
  repeat step || simp_red.
Qed.

Lemma open_reducible_false:
  forall Θ Γ,
    [ Θ; Γ ⊨ tfalse : T_bool ].
Proof.
  unfold open_reducible,reduces_to, closed_term in *; steps;
    eauto using reducible_false with star.
Qed.

Lemma reducible_ite:
  forall ρ T b t1 t2,
    wf t1 0 ->
    wf t2 0 ->
    pfv t1 term_var = nil ->
    pfv t2 term_var = nil ->
    is_erased_term t1 ->
    is_erased_term t2 ->
    valid_interpretation ρ ->
    [ ρ ⊨ b : T_bool ] ->
    ([ b ≡ ttrue ] -> [ ρ ⊨ t1 : T ]) ->
    ([ b ≡ tfalse ] -> [ ρ ⊨ t2 : T ]) ->
    [ ρ ⊨ ite b t1 t2 : T ].
Proof.
  repeat step || top_level_unfold reduces_to ||
         top_level_unfold closed_term ||
         simp_red.

  - apply star_backstep_reducible with (ite ttrue t1 t2); repeat step || list_utils;
      auto with cbvlemmas; eauto with fv; eauto with wf.
    eapply backstep_reducible; repeat step || list_utils;
      eauto 2 with smallstep;
      eauto with fv;
      eauto with wf;
      eauto using equivalent_star.

  - apply star_backstep_reducible with (ite tfalse t1 t2); repeat step || list_utils;
      auto with cbvlemmas; eauto with fv; eauto with wf.
    eapply backstep_reducible; repeat step || list_utils;
      eauto 2 with smallstep;
      eauto with fv;
      eauto with wf;
      eauto using equivalent_star.
Qed.

Lemma open_reducible_ite:
  forall Θ Γ T b t1 t2 x,
    wf t1 0 ->
    wf t2 0 ->
    subset (fv t1) (support Γ) ->
    subset (fv t2) (support Γ) ->
    ~(x ∈ fv b) ->
    ~(x ∈ fv T) ->
    ~(x ∈ fv_context Γ) ->
    ~(x ∈ Θ) ->
    is_erased_term b ->
    is_erased_term t1 ->
    is_erased_term t2 ->
    [ Θ; Γ ⊨ b : T_bool ] ->
    [ Θ; (x, T_equiv b ttrue) :: Γ ⊨ t1 : T ] ->
    [ Θ; (x, T_equiv b tfalse) :: Γ ⊨ t2 : T ] ->
    [ Θ; Γ ⊨ ite b t1 t2 : T ].
Proof.
  intros; unfold open_reducible; steps.

  unfold open_reducible in *; apply reducible_ite; repeat step || t_termlist;
    eauto with wf;
    eauto using subset_same with fv;
    eauto with erased.

  - unshelve epose proof (H11 _ ((x, uu) :: lterms) _ _ _);
      repeat step || apply SatCons || list_utils || simp_red || t_substitutions.
  - unshelve epose proof (H12 _ ((x, uu) :: lterms) _ _ _);
      repeat step || apply SatCons || list_utils || simp_red || t_substitutions.
Qed.
