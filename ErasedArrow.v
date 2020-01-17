Require Import Equations.Equations.
Require Import Coq.Lists.List.

Require Export SystemFR.ReducibilityStep.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducible_lambda:
  forall theta t U V,
    is_erased_term t ->
    wf U 0 ->
    wf t 1 ->
    pfv U term_var = nil ->
    pfv t term_var = nil ->
    pfv t type_var = nil ->
    valid_interpretation theta ->
    is_erased_type V ->
    (forall u, reducible_values theta u U -> reducible theta (open 0 t u) (open 0 V u)) ->
    reducible_values theta (notype_lambda t) (T_arrow U V).
Proof.
  repeat step || t_listutils || simp reducible_values in * || unfold closed_value, closed_term ||
         rewrite reducibility_rewrite;
    eauto 2 with cbvlemmas.

  apply backstep_reducible with (open 0 t a); repeat step || t_listutils;
    eauto 2 with fv;
    eauto 2 with wf;
    eauto using red_is_val with smallstep.
Qed.

Lemma open_reducible_lambda:
  forall tvars gamma x t U V,
    wf U 0 ->
    wf t 1 ->
    subset (fv_context gamma) (support gamma) ->
    subset (fv U) (support gamma) ->
    subset (fv t) (support gamma) ->
    ~(x ∈ support gamma) ->
    ~(x ∈ fv t) ->
    ~(x ∈ fv V) ->
    is_erased_term t ->
    is_erased_type V ->
    open_reducible tvars ((x, U) :: gamma) (open 0 t (term_fvar x)) (open 0 V (term_fvar x)) ->
    open_reducible tvars gamma (notype_lambda t) (T_arrow U V).
Proof.
  unfold open_reducible in *; steps.

  apply reducible_value_expr; repeat step.
  apply reducible_lambda; tac1;
    eauto with wf;
    eauto with fv;
    eauto with erased.

  unshelve epose proof (H9 theta ((x,u) :: lterms) _ _ _); repeat tac1 || t_sets;
    eauto using reducible_let with erased.
Qed.

Lemma reducible_app:
  forall theta U V t1 t2,
    valid_interpretation theta ->
    is_erased_type V ->
    wf V 1 ->
    reducible theta t1 (T_arrow U V) ->
    reducible theta t2 U ->
    reducible theta (app t1 t2) (open 0 V t2).
Proof.
  intros theta U V t1 t2 H1 H2.
  unfold reducible, reduces_to in *;
    repeat step || t_listutils || simp reducible_values in * || unfold reduces_to in *;
    t_closer.

  lazymatch goal with
  | H1: forall a, _,
    H2: reducible_values _ ?v _ |- _ =>
    unshelve epose proof (H1 v _); steps; eauto with erased
  end; unfold closed_value, closed_term in *; repeat step || t_listutils.

  exists v1; repeat step || simp reducible_values in *;
    eauto using star_trans with cbvlemmas values;
    t_closer;
    eauto using reducibility_values_rtl.
Qed.

Lemma reducible_app2:
  forall theta e1 e2 U V,
    wf V 0 ->
    valid_interpretation theta ->
    reducible theta e1 (T_arrow U V) ->
    reducible theta e2 U ->
    reducible theta (app e1 e2) V.
Proof.
  intros; unfold reducible in *; unfold reduces_to in *;
    repeat step || t_listutils || simp reducible_values in * || instantiate_any || unfold reduces_to in *;
      t_closer.

  match goal with
  | H: forall a, _ |- _ => unshelve epose proof (H v _); steps; eauto with erased
  end.

  rewrite open_none in *; auto.
  eexists; repeat step || t_closing; eauto;
    eauto using star_trans with cbvlemmas values.
Qed.

Lemma open_reducible_app:
  forall tvars gamma U V t1 t2,
    is_erased_type V ->
    wf V 1 ->
    open_reducible tvars gamma t1 (T_arrow U V) ->
    open_reducible tvars gamma t2 U ->
    open_reducible tvars gamma (app t1 t2) (open 0 V t2).
Proof.
  unfold open_reducible in *; tac1;
    eapply reducible_app; eauto with erased.
    try solve [ unshelve eauto with wf; auto ].
Qed.

Lemma reducible_app_sem:
  forall theta e u U V T,
    valid_interpretation theta ->
    is_erased_type V ->
    wf V 1 ->
    reducible theta e (T_arrow U V) ->
    reducible_values theta u U ->
    T = open 0 V u ->
    reducible theta (app e u) T.
Proof.
  steps.
  eauto using reducible_app, reducible_value_expr, red_is_val.
Qed.
