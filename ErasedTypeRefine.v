Require Import Equations.Equations.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Export SystemFR.ErasedLet.
Require Export SystemFR.ReducibilityOpenEquivalent.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducible_type_refine:
  forall ρ t1 t2 A B,
    valid_interpretation ρ ->
    is_erased_type B ->
    wf B 1 ->
    fv B = nil ->
    [ ρ ⊨ t1 : A ] ->
    [ ρ ⊨ t2 : open 0 B t1 ] ->
    [ ρ ⊨ t1 : T_type_refine A B ].
Proof.
  unfold reduces_to in *; repeat step;
    eauto with wf; eauto with fv.

  eexists; steps; eauto;
    repeat step || simp_red; t_closer.
  eexists; eapply reducibility_values_ltr; eauto; steps;
    t_closer.
Qed.

Lemma reducible_type_refine2:
  forall ρ t A B,
    valid_interpretation ρ ->
    [ ρ ⊨ t : T_type_refine A B ] ->
    [ ρ ⊨ t : A ].
Proof.
  unfold reduces_to; repeat step || simp_red; eauto.
Qed.

Lemma open_reducible_type_refine:
  forall Θ Γ t1 t2 A B,
    is_erased_type B ->
    wf B 1 ->
    subset (fv B) (support Γ) ->
    [ Θ; Γ ⊨ t1 : A ] ->
    [ Θ; Γ ⊨ t2 : open 0 B t1 ] ->
    [ Θ; Γ ⊨ t1 : T_type_refine A B ].
Proof.
  unfold open_reducible;
    repeat step || t_instantiate_sat3 || t_substitutions;
    try solve [
      eapply reducible_type_refine;
      eauto with erased fv;
      try solve [ unshelve eauto with wf; auto ]
    ].
Qed.

Lemma open_reducible_get_refinement_witness:
  forall Θ Γ t1 t2 A B T x,
    ~(x ∈ Θ) ->
    ~(x ∈ fv_context Γ) ->
    ~(x ∈ fv t1) ->
    ~(x ∈ fv t2) ->
    ~(x ∈ fv T) ->
    ~(x ∈ fv A) ->
    ~(x ∈ fv B) ->
    wf t1 0 ->
    wf t2 0 ->
    wf B 1 ->
    is_erased_term t2 ->
    subset (fv t1) (support Γ) ->
    subset (fv t2) (support Γ) ->
    subset (fv B) (support Γ) ->
    [ Θ; Γ ⊨ t1 : T_type_refine A B ] ->
    [ Θ; (x, open 0 B t1) :: Γ ⊨ t2 : T ] ->
    [ Θ; Γ ⊨ app (notype_lambda t2) uu : T ].
Proof.
  unfold open_reducible; repeat step || t_instantiate_sat3.
  eapply backstep_reducible; eauto with smallstep values;
    repeat step || list_utils; eauto with fv wf erased.
  rewrite open_none; eauto with wf.
  top_level_unfold reduces_to; repeat step || simp_red.

  unshelve epose proof (H14 ρ ((x, p) :: lterms) _ _ _);
    repeat step || list_utils || apply SatCons || t_substitutions || fv_open;
    t_closer;
    eauto with twf.
  eapply reducibility_values_rtl; eauto;
    repeat step;
    t_closer.
Qed.
