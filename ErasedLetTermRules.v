Require Import Equations.Equations.

Require Import Coq.Lists.List.

Require Export SystemFR.RedTactics.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducible_value_let:
  forall theta v t A B,
    wf t 1 ->
    pfv t term_var = nil ->
    is_erased_term t ->
    valid_interpretation theta ->
    reducible_values theta v A ->
    reducible theta (open 0 t v) B ->
    reducible theta (app (notype_lambda t) v) B.
Proof.
  steps.
  eapply backstep_reducible; eauto using red_is_val with smallstep;
    repeat step || t_listutils;
    eauto 2 with fv;
    eauto 2 with wf;
    eauto with erased.
Qed.

Lemma reducible_let_rule:
  forall theta t1 t2 A B,
    wf t2 1 ->
    fv t2 = nil ->
    valid_interpretation theta ->
    reducible theta t1 A ->
    is_erased_term t2 ->
    (forall v,
        cbv_value v ->
        star scbv_step t1 v ->
        reducible theta (open 0 t2 v) B) ->
    reducible theta (app (notype_lambda t2) t1) B.
Proof.
  unfold reducible, reduces_to, closed_term; repeat step || t_listutils; eauto with fv.
  createHypothesis;
    repeat step || t_values_info2.
  eexists; steps; eauto.
  eapply star_trans; eauto with cbvlemmas.
  eapply star_trans;
    eauto with cbvlemmas values;
    eauto with star smallstep.
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
    is_erased_term t2 ->
    subset (fv A) (support gamma) ->
    subset (fv t2) (support gamma) ->
    open_reducible tvars gamma t1 A ->
    open_reducible tvars ((p, T_equiv (fvar x term_var) t1) :: (x,A) :: gamma)
                   (open 0 t2 (fvar x term_var)) B ->
    open_reducible tvars gamma (app (notype_lambda t2) t1) B.
Proof.
  unfold open_reducible; steps.

  eapply reducible_let_rule;
   repeat step || top_level_unfold reducible || top_level_unfold reduces_to ||
          t_values_info2 || t_deterministic_star || t_termlist || t_instantiate_sat4;
      unshelve eauto with wf; eauto using subset_same with fv;
        eauto with erased.

  match goal with
  | H: star scbv_step _ ?v |- _ =>
    unshelve epose proof (H15 theta ((p, uu) :: (x, v) :: lterms) _ _)
  end; tac1;
    eauto with erased;
    try solve [ apply equivalent_sym, equivalent_star; steps; eauto with wf erased ].
Qed.

(*
Lemma reducible_value_let2:
  forall theta v t A B,
    wf t 1 ->
    pfv t term_var = nil ->
    is_erased_term t ->
    valid_interpretation theta ->
    is_erased_type B ->
    reducible_values theta v A ->
    reducible theta (open 0 t v) (open 0 B v) ->
    reducible theta (app (notype_lambda t) v) (T_let v B).
Proof.
  steps.
  eapply backstep_reducible; eauto using red_is_val with smallstep;
    repeat step || t_listutils;
    eauto 2 with fv;
    eauto 2 with wf;
    eauto with erased;
    eauto using reducible_let.
Qed.

Lemma reducible_let2_rule:
  forall theta t1 t2 A B,
    wf t2 1 ->
    fv t2 = nil ->
    valid_interpretation theta ->
    reducible theta t1 A ->
    is_erased_term t2 ->
    is_erased_type B ->
    (forall v,
        cbv_value v ->
        star scbv_step t1 v ->
        reducible theta (open 0 t2 v) (open 0 B v)) ->
    reducible theta (app (notype_lambda t2) t1) (T_let t1 B).
Proof.
  unfold reducible, reduces_to, closed_term; repeat step || t_listutils; eauto with fv.
  createHypothesis;
    repeat step || t_values_info2.

  exists v0; steps; eauto.
  + eapply reducible_let_backstep_values; eauto.
    eauto using reducible_val_let.
  + eapply star_trans; eauto with cbvlemmas.
    eapply star_trans; eauto with cbvlemmas values.
    eapply star_trans;
      eauto with cbvlemmas;
      eauto with smallstep.
Qed.
*)

(*
Lemma open_reducible_let2:
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
    is_erased_term t2 ->
    subset (fv A) (support gamma) ->
    subset (fv t2) (support gamma) ->
    is_erased_type B ->
    open_reducible tvars gamma t1 A ->
    open_reducible tvars ((p, T_equiv (fvar x term_var) t1) :: (x,A) :: gamma)
                   (open 0 t2 (fvar x term_var)) (open 0 B (fvar x term_var)) ->
    open_reducible tvars gamma (app (notype_lambda t2) t1) (T_let t1 B).
Proof.
  unfold open_reducible; steps.

  eapply reducible_let2_rule;
   repeat step || top_level_unfold reducible || top_level_unfold reduces_to ||
          t_values_info2 || t_deterministic_star || t_termlist || t_instantiate_sat4;
      unshelve eauto with wf; eauto using subset_same with fv;
        eauto with erased.

  match goal with
  | H: star scbv_step _ ?v |- _ =>
    unshelve epose proof (H16 theta ((p, uu) :: (x, v) :: lterms) _ _); tac1;
      eauto 3 using equivalent_sym with b_equiv;
      eauto with erased
  end.
Qed.
*)
