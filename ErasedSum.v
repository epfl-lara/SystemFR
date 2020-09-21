Require Import Equations.Equations.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Require Export SystemFR.ErasedLet2.
Require Export SystemFR.ReducibilityOpenEquivalent.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducible_left:
  forall ρ t A B,
    valid_interpretation ρ ->
    [ ρ ⊨ t : A ] ->
    [ ρ ⊨ tleft t : T_sum A B ].
Proof.
  unfold reduces_to; steps.
  eexists; steps; eauto with cbvlemmas;
    repeat step || simp_red || t_closing; eauto with values.
Qed.

Lemma open_reducible_left:
  forall Θ Γ t A B,
    [ Θ; Γ ⊨ t : A ] ->
    [ Θ; Γ ⊨ tleft t : T_sum A B ].
Proof.
  unfold open_reducible; steps; eauto using reducible_left.
Qed.

Lemma reducible_right:
  forall ρ t A B,
    valid_interpretation ρ ->
    [ ρ ⊨ t : B ] ->
    [ ρ ⊨ tright t : T_sum A B ].
Proof.
  unfold reduces_to; steps.
  eexists; steps; eauto with cbvlemmas;
    repeat step || simp_red || t_closing; eauto with values.
Qed.

Lemma open_reducible_right:
  forall Θ Γ t A B,
    [ Θ; Γ ⊨ t : B ] ->
    [ Θ; Γ ⊨ tright t : T_sum A B ].
Proof.
  unfold open_reducible; steps; eauto using reducible_right.
Qed.

Lemma open_reducible_sum_match:
  forall Θ Γ t tl tr T1 T2 T y p,
    subset (fv t) (support Γ) ->
    subset (fv tl) (support Γ) ->
    subset (fv tr) (support Γ) ->
    subset (fv T1) (support Γ) ->
    subset (fv T2) (support Γ) ->
    subset (fv T) (support Γ) ->
    wf T 1 ->
    wf T1 0 ->
    wf T2 0 ->
    wf t 0 ->
    wf tr 1 ->
    wf tl 1 ->
    ~(y ∈ fv_context Γ) ->
    ~(y ∈ fv T) ->
    ~(y ∈ fv T1) ->
    ~(y ∈ fv T2) ->
    ~(y ∈ pfv T term_var) ->
    ~(p ∈ pfv_context Γ term_var) ->
    ~(p ∈ pfv t term_var) ->
    ~(p ∈ pfv T1 term_var) ->
    ~(p ∈ pfv T2 term_var) ->
    ~(p ∈ pfv T term_var) ->
    ~(p = y) ->
    is_erased_term t ->
    is_erased_term tl ->
    is_erased_term tr ->
    is_erased_type T ->
    [ Θ; Γ ⊨ t : T_sum T1 T2 ] ->
    [ Θ; (p, T_equiv t (tleft (fvar y term_var))) :: (y, T1) :: Γ ⊨
        open 0 tl (fvar y term_var) : open 0 T (tleft (fvar y term_var)) ] ->
    [ Θ; (p, T_equiv t (tright (fvar y term_var))) :: (y, T2) :: Γ ⊨
        open 0 tr (fvar y term_var) : open 0 T (tright (fvar y term_var)) ] ->
    [ Θ; Γ ⊨ sum_match t tl tr : open 0 T t ].
Proof.
  unfold open_reducible; repeat step || t_instantiate_sat3 || top_level_unfold reduces_to || simp_red || t_substitutions.

  - eapply reducibility_rtl; eauto; t_closer.

    unshelve epose proof (H27 ρ ((p, uu) :: (y,v') :: lterms) _ _ _);
      repeat step || apply SatCons || list_utils || t_substitutions || simp_red ||
             t_values_info2 || t_deterministic_star;
      try solve [ equivalent_star ];
      t_closer;
      eauto with twf.

    eapply star_backstep_reducible; eauto with cbvlemmas;
      repeat step || list_utils; t_closer.
    eapply backstep_reducible; eauto with smallstep;
      repeat step || list_utils; t_closer.

  - eapply reducibility_rtl; eauto; t_closer.

    unshelve epose proof (H28 ρ ((p, uu) :: (y,v') :: lterms) _ _ _);
      repeat step || apply SatCons || list_utils || t_substitutions || simp_red ||
             t_values_info2 || t_deterministic_star;
      try solve [ equivalent_star ];
      t_closer;
      eauto with twf.

    eapply star_backstep_reducible; eauto with cbvlemmas;
      repeat step || list_utils; t_closer.
    eapply backstep_reducible; eauto with smallstep;
      repeat step || list_utils; t_closer.
Qed.
