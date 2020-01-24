Require Import Equations.Equations.

Require Import Coq.Lists.List.

Require Export SystemFR.RedTactics.
Require Export SystemFR.ReducibilityOpenEquivalent.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducible_value_let:
  forall theta v t A B,
    wf t 1 ->
    pfv t term_var = nil ->
    is_erased_term t ->
    valid_interpretation theta ->
    is_erased_type B ->
    reducible_values theta v A ->
    reducible theta (open 0 t v) (open 0 B v) ->
    reducible theta (app (notype_lambda t) v) (open 0 B v).
Proof.
  steps.
  eapply backstep_reducible; eauto using red_is_val with smallstep;
    repeat step || list_utils;
    eauto 2 with fv;
    eauto 2 with wf;
    eauto with erased.
Qed.

Lemma reducible_let:
  forall theta t1 t2 A B,
    wf t2 1 ->
    wf B 1 ->
    fv t2 = nil ->
    valid_interpretation theta ->
    reducible theta t1 A ->
    is_erased_term t2 ->
    is_erased_type B ->
    fv B = nil ->
    (forall v,
        cbv_value v ->
        star scbv_step t1 v ->
        reducible theta (open 0 t2 v) (open 0 B v)) ->
    reducible theta (app (notype_lambda t2) t1) (open 0 B t1).
Proof.
  unfold reducible, reduces_to, closed_term; repeat step || list_utils; eauto with fv.
  createHypothesis;
    repeat step || t_values_info2.

  exists v0; steps; eauto using reducibility_values_rtl.
  eapply star_trans; eauto with cbvlemmas.
  eapply star_trans; eauto with cbvlemmas values.
  eapply star_trans;
    eauto with cbvlemmas;
    eauto with star smallstep.
Qed.

Lemma reducible_let2:
  forall theta t1 t2 A B,
    wf t2 1 ->
    wf B 0 ->
    fv t2 = nil ->
    valid_interpretation theta ->
    reducible theta t1 A ->
    is_erased_term t2 ->
    is_erased_type B ->
    fv B = nil ->
    (forall v,
        cbv_value v ->
        star scbv_step t1 v ->
        reducible theta (open 0 t2 v) B) ->
    reducible theta (app (notype_lambda t2) t1) B.
Proof.
  intros.
  rewrite <- (open_none B 0 t1); steps.
  eapply reducible_let; eauto with wf;
    repeat step || rewrite (open_none B) by auto.
Qed.

Lemma open_reducible_let:
  forall tvars gamma t1 t2 A B x p,
    ~(p ∈ fv_context gamma) ->
    ~(p ∈ fv A) ->
    ~(p ∈ fv B) ->
    ~(p ∈ fv t1) ->
    ~(p ∈ fv t2) ->
    ~(x ∈ fv_context gamma) ->
    ~(x ∈ fv A) ->
    ~(x ∈ fv B) ->
    ~(x ∈ fv t1) ->
    ~(x ∈ fv t2) ->
    ~(x = p) ->
    wf t2 1 ->
    wf B 1 ->
    is_erased_term t2 ->
    subset (fv A) (support gamma) ->
    subset (fv B) (support gamma) ->
    subset (fv t2) (support gamma) ->
    is_erased_type B ->
    [ tvars; gamma ⊨ t1 : A ] ->
    [ tvars; (p, T_equiv (fvar x term_var) t1) :: (x,A) :: gamma ⊨
        open 0 t2 (fvar x term_var) : open 0 B (fvar x term_var) ] ->
    [ tvars; gamma ⊨ app (notype_lambda t2) t1 : open 0 B t1 ].
Proof.
  unfold open_reducible; repeat step || t_substitutions.

  eapply reducible_let;
   repeat step || top_level_unfold reducible || top_level_unfold reduces_to ||
          t_values_info2 || t_deterministic_star || t_termlist || t_instantiate_sat4;
      unshelve eauto with wf; eauto using subset_same with fv;
        eauto with erased.

  match goal with
  | H: star scbv_step _ ?v |- _ =>
    unshelve epose proof (H18 theta ((p, uu) :: (x, v) :: lterms) _ _)
  end;
    repeat step || apply SatCons || list_utils || t_substitutions || simp_red;
    t_closer;
    try solve [ apply equivalent_sym; equivalent_star ];
    eauto with twf.
Qed.
