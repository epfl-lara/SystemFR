Require Import Equations.Equations.

Require Import Coq.Lists.List.

Require Export SystemFR.RedTactics.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducible_value_let:
  forall ρ v t A B,
    wf t 1 ->
    pfv t term_var = nil ->
    is_erased_term t ->
    valid_interpretation ρ ->
    [ ρ ⊨ v : A ]v ->
    [ ρ ⊨ open 0 t v : B ] ->
    [ ρ ⊨ app (notype_lambda t) v : B ].
Proof.
  steps.
  eapply backstep_reducible; eauto using red_is_val with smallstep;
    repeat step || list_utils;
    eauto 2 with fv;
    eauto 2 with wf;
    eauto with erased.
Qed.

Lemma reducible_let_rule:
  forall ρ t1 t2 A B,
    wf t2 1 ->
    fv t2 = nil ->
    valid_interpretation ρ ->
    [ ρ ⊨ t1 : A ] ->
    is_erased_term t2 ->
    (forall v,
        cbv_value v ->
        t1 ~>* v ->
        [ ρ ⊨ open 0 t2 v : B ]) ->
    [ ρ ⊨ app (notype_lambda t2) t1 : B ].
Proof.
  unfold reduces_to, closed_term; repeat step || list_utils; eauto with fv.
  createHypothesis;
    repeat step || t_values_info2.
  eexists; steps; eauto.
  eapply star_trans; eauto with cbvlemmas.
  eapply star_trans;
    eauto with cbvlemmas values;
    eauto with star smallstep.
Qed.

Lemma open_reducible_let:
  forall Θ Γ t1 t2 A B x p,
    ~(p ∈ fv_context Γ) ->
    ~(p ∈ fv A) ->
    ~(p ∈ fv B) ->
    ~(p ∈ fv t1) ->
    ~(p ∈ fv t2) ->
    ~(x ∈ fv_context Γ) ->
    ~(x ∈ fv A) ->
    ~(x ∈ fv B) ->
    ~(x ∈ fv t1) ->
    ~(x ∈ fv t2) ->
    ~(x = p) ->
    wf t2 1 ->
    is_erased_term t2 ->
    subset (fv A) (support Γ) ->
    subset (fv t2) (support Γ) ->
    [ Θ; Γ ⊨ t1 : A ] ->
    [ Θ; (p, T_equiv (fvar x term_var) t1) :: (x,A) :: Γ ⊨
        open 0 t2 (fvar x term_var) : B ] ->
    [ Θ; Γ ⊨ app (notype_lambda t2) t1 : B ].
Proof.
  unfold open_reducible; steps.

  eapply reducible_let_rule;
   repeat step || top_level_unfold reduces_to ||
          t_values_info2 || t_deterministic_star || t_termlist || t_instantiate_sat4;
      unshelve eauto with wf; eauto using subset_same with fv;
        eauto with erased.

  match goal with
  | H: _ ~>* ?v |- _ =>
    unshelve epose proof (H15 ρ ((p, uu) :: (x, v) :: lterms) _ _)
  end;
    repeat step || list_utils || apply SatCons || t_substitutions || simp_red;
    t_closer;
    try solve [ apply equivalent_sym; equivalent_star ];
    eauto with twf.
Qed.
