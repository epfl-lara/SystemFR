Require Import Coq.Lists.List.

Require Export SystemFR.ReducibilitySubst.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducibility_candidate_empty:
  reducibility_candidate (fun _ => False).
Proof.
  unfold reducibility_candidate; steps.
Qed.

Lemma reducible_type_abs:
  forall theta t T X,
    fv t = nil ->
    fv T = nil ->
    wf t 0 ->
    wf T 1 ->
    is_erased_term t ->
    valid_interpretation theta ->
    (X ∈ pfv T type_var -> False) ->
    (X ∈ support theta -> False) ->
    (forall RC,
      reducibility_candidate RC ->
      reducible ((X,RC) :: theta) t (topen 0 T (fvar X type_var))) ->
    reducible theta t (T_abs T).
Proof.
  intros.
  unshelve epose proof (H7 (fun _ => False) _); steps; eauto using reducibility_candidate_empty; t_closing.

  unfold reducible, reduces_to in *; repeat step || simp_red; t_closing.
  exists v; repeat step || simp_red; t_closing;
    eauto 3 using red_is_val, reducibility_candidate_empty with step_tactic.
  exists X; steps.
  instantiate_any; repeat step || t_deterministic_star;
    eauto 3 using red_is_val, reducibility_candidate_empty with step_tactic.
Qed.

Lemma open_reducible_type_abs:
  forall tvars gamma t T (X : nat),
    subset (pfv t term_var) (support gamma) ->
    subset (pfv T term_var) (support gamma) ->
    wf t 0 ->
    wf T 1 ->
    (X ∈ pfv_context gamma term_var -> False) ->
    (X ∈ pfv_context gamma type_var -> False) ->
    (X ∈ pfv t term_var -> False) ->
    (X ∈ pfv T term_var -> False) ->
    (X ∈ pfv T type_var -> False) ->
    (X ∈ tvars -> False) ->
    is_erased_term t ->
    open_reducible (X :: tvars) gamma t (topen 0 T (fvar X type_var)) ->
    open_reducible tvars gamma t (T_abs T).
Proof.
  unfold open_reducible; repeat step || t_termlist.

  apply reducible_type_abs with X;
    repeat step || rewrite fv_subst_different_tag in * by (steps; eauto with fv);
      eauto with wf;
      eauto with fv;
      eauto with erased.

  match goal with
  | H: forall _ _, _ |- _ =>
      unshelve epose proof (H ((X,RC) :: theta) lterms _ _ _); tac1
  end;
    eauto using satisfies_unused.
Qed.

Lemma reducible_inst:
  forall theta t U V,
    wf V 0 ->
    twf V 0 ->
    pfv V term_var = nil ->
    wf U 0 ->
    pfv U term_var = nil ->
    valid_interpretation theta ->
    is_erased_type U ->
    is_erased_type V ->
    reducible theta t (T_abs U) ->
    reducible theta t (topen 0 U V).
Proof.
  unfold reducible, reduces_to in *;
    repeat step || list_utils || simp_red || unfold reduces_to in *.
  match goal with
  | H: forall RC, reducibility_candidate RC -> _ |- _ =>
      unshelve epose proof (H (fun v => reducible_values theta v V) _); steps;
        eauto using reducibility_is_candidate
  end.
  exists v; steps; eauto using star_trans with cbvlemmas.
  apply (reducible_rename_one _ _ _ _ _ (makeFresh (pfv U type_var :: pfv V type_var :: nil))) in H12;
    repeat step || finisher; eauto using reducibility_is_candidate.
  eapply reducibility_subst_head; eauto; repeat step || list_utils || finisher.
Qed.

Lemma open_reducible_inst:
  forall tvars (gamma : context) t U V,
    wf U 0 ->
    wf V 0 ->
    twf V 0 ->
    is_erased_type U ->
    is_erased_type V ->
    subset (fv U) (support gamma) ->
    subset (fv V) (support gamma) ->
    open_reducible tvars gamma t (T_abs U) ->
    open_reducible tvars gamma t (topen 0 U V).
Proof.
  unfold open_reducible;
    repeat step || t_instantiate_sat3 || rewrite substitute_topen || apply reducible_inst ||
      rewrite fv_subst_different_tag in * by (steps; eauto with fv);
    t_closer;
    eauto with btwf.
Qed.
