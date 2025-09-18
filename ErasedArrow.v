From Equations Require Import Equations.
From Stdlib Require Import List.

Require Export SystemFR.ReducibilityOpenEquivalent.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducible_lambda:
  forall ρ t U V,
    is_erased_term t ->
    wf U 0 ->
    wf t 1 ->
    pfv U term_var = nil ->
    pfv t term_var = nil ->
    valid_interpretation ρ ->
    is_erased_type V ->
    (forall u, [ ρ ⊨ u : U ]v -> [ ρ ⊨ open 0 t u : open 0 V u ]) ->
    [ ρ ⊨ notype_lambda t : T_arrow U V ]v.
Proof.
  repeat step || list_utils || simp_red_goal ||
         unfold closed_value, closed_term ||
         rewrite reducibility_rewrite;
    eauto 2 with cbvlemmas.

  apply backstep_reducible with (open 0 t a); repeat step || list_utils;
    eauto 2 with fv;
    eauto 2 with wf;
    eauto using red_is_val with smallstep.
Qed.

Lemma open_reducible_lambda:
  forall Θ Γ x t U V,
    wf U 0 ->
    wf t 1 ->
    subset (fv_context Γ) (support Γ) ->
    subset (fv U) (support Γ) ->
    subset (fv t) (support Γ) ->
    ~(x ∈ support Γ) ->
    ~(x ∈ fv t) ->
    ~(x ∈ fv V) ->
    is_erased_term t ->
    is_erased_type V ->
    [ Θ; (x, U) :: Γ ⊨ open 0 t (fvar x term_var) : open 0 V (fvar x term_var) ] ->
    [ Θ; Γ ⊨ notype_lambda t : T_arrow U V ].
Proof.
  unfold open_reducible in *; steps.

  apply reducible_value_expr; repeat step.
  apply reducible_lambda; repeat step;
    eauto with wf;
    eauto with fv;
    eauto with erased.

  unshelve epose proof (H9 ρ ((x,u) :: lterms) _ _ _);
    repeat step || apply SatCons || t_substitutions;
    eauto with fv wf twf.
Qed.

Lemma reducible_app:
  forall ρ U V t1 t2,
    valid_interpretation ρ ->
    is_erased_type V ->
    wf V 1 ->
    pfv V term_var = nil ->
    [ ρ ⊨ t1 : T_arrow U V ] ->
    [ ρ ⊨ t2 : U ]  ->
    [ ρ ⊨ app t1 t2 : open 0 V t2 ].
Proof.
  intros ρ U V t1 t2 H1 H2.
  unfold reduces_to in *;
    repeat step || list_utils || simp_red || unfold reduces_to in *;
    t_closer.

  lazymatch goal with
  | H1: forall a, _,
    H2: [ _ ⊨ ?v : _ ]v |- _ =>
    unshelve epose proof (H1 v _ _ _)
  end; steps; unfold closed_value, closed_term in *; repeat step || list_utils;
    eauto with erased wf fv.

  exists v1; repeat step || simp_red;
    eauto using star_trans with cbvlemmas values;
    t_closer;
    eauto using reducibility_values_rtl.
Qed.

Lemma reducible_app2:
  forall ρ e1 e2 U V,
    wf V 0 ->
    valid_interpretation ρ ->
    [ ρ ⊨ e1 : T_arrow U V ] ->
    [ ρ ⊨ e2 : U ]  ->
    [ ρ ⊨ app e1 e2 : V ].
Proof.
  intros; unfold reduces_to in *;
    repeat step || list_utils || simp_red || instantiate_any || unfold reduces_to in *;
      t_closer.

  match goal with
  | H: forall a, _ |- _ => unshelve epose proof (H v _ _ _ _)
  end; steps; eauto with erased wf fv.

  rewrite open_none in *; auto.
  eexists; repeat step || t_closing; eauto;
    eauto using star_trans with cbvlemmas values.
Qed.

Lemma open_reducible_app:
  forall Θ Γ U V t1 t2,
    is_erased_type V ->
    wf V 1 ->
    subset (fv V) (support Γ) ->
    [ Θ; Γ ⊨ t1 : T_arrow U V ] ->
    [ Θ; Γ ⊨ t2 : U ] ->
    [ Θ; Γ ⊨  app t1 t2 : open 0 V t2 ].
Proof.
  unfold open_reducible in *;
    repeat step || t_substitutions;
    eapply reducible_app;
    eauto with erased;
    try solve [ unshelve eauto with wf; auto ];
    eauto with fv.
Qed.
