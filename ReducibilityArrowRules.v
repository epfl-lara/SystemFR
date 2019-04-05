Require Import Equations.Equations.
Require Import Coq.Lists.List.

Require Import SystemFR.Syntax.
Require Import SystemFR.Tactics.
Require Import SystemFR.ListUtils.
Require Import SystemFR.Sets.
Require Import SystemFR.AssocList.
Require Import SystemFR.Freshness.
Require Import SystemFR.SubstitutionLemmas.
Require Import SystemFR.TermList.
Require Import SystemFR.StarLemmas.
Require Import SystemFR.SetLemmas.
Require Import SystemFR.StarRelation.
Require Import SystemFR.SmallStep.
Require Import SystemFR.SubstitutionErase.
Require Import SystemFR.TermListReducible.

Require Import SystemFR.ReducibilityCandidate.
Require Import SystemFR.ReducibilityDefinition.
Require Import SystemFR.ReducibilityLemmas.
Require Import SystemFR.ReducibilityLetRules.
Require Import SystemFR.RedTactics.


Require Import SystemFR.WFLemmas.
Require Import SystemFR.WFLemmasLists.

Require Import SystemFR.FVLemmas.
Require Import SystemFR.FVLemmasLists.

Opaque reducible_values.
Opaque makeFresh.

Set Program Mode.

Lemma reducible_lambda:
  forall theta t U V,
    is_erased_term t ->
    wf U 0 ->
    wf t 1 ->
    pfv U term_var = nil ->
    pfv t term_var = nil ->
    pfv t type_var = nil ->
    valid_interpretation theta ->
    (forall u, reducible_values theta u U -> reducible theta (open 0 t u) (T_let u V)) ->
    reducible_values theta (notype_lambda t) (T_arrow U V).
Proof.
  repeat step || t_listutils || simp reducible_values in * || unfold closed_value, closed_term ||
         rewrite reducibility_rewrite;
    eauto 2 with bsteplemmas.

  apply backstep_reducible with (open 0 t a); repeat step || t_listutils;
    eauto 2 with bfv;
    eauto 2 with bwf;
    eauto using red_is_val with smallstep.
  eauto using reducible_let2, red_is_val.
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
    open_reducible tvars ((x, U) :: gamma) (open 0 t (term_fvar x)) (open 0 V (term_fvar x)) ->
    open_reducible tvars gamma (notype_lambda t) (T_arrow U V).
Proof.
  unfold open_reducible in *; steps.

  apply reducible_value_expr; repeat step.
  apply reducible_lambda; tac1;
    eauto with bwf;
    eauto with bfv;
    eauto with berased.

  - unshelve epose proof (H8 theta ((x,u) :: lterms) _ _ _); repeat tac1 || t_sets;
      eauto using reducible_let.
Qed.

Lemma reducible_app:
  forall theta U V t1 t2,
    valid_interpretation theta ->
    reducible theta t1 (T_arrow U V) ->
    reducible theta t2 U ->
    reducible theta (app t1 t2) (T_let t2 V).
Proof.
  intros theta U V t1 t2 H1 H2.
  unfold reducible, reduces_to in *;
    repeat step || t_listutils || simp reducible_values in * || unfold reduces_to in *;
    t_closer.

  match goal with
  | H: forall a, _ |- _ => unshelve epose proof (H t' _); steps; eauto with berased
  end; unfold closed_value, closed_term in *; repeat step || t_listutils.
  exists t'1; repeat step || simp reducible_values in *;
    eauto using star_smallstep_trans with bsteplemmas values;
    t_closer.
  unshelve exists t';
    repeat step || simp reducible_values in *;
      eauto using red_is_val; eauto with berased.
Qed.

Lemma reducible_app2:
  forall theta e1 e2 U V,
    wf V 0 ->
    valid_interpretation theta ->
    reducible theta e1 (T_arrow U V) ->
    reducible theta e2 U ->
    reducible theta (app e1 e2) V.
Proof.
  intros e1 e2 U V W H1 H2;
    unfold reducible in *;
    unfold reduces_to in *;
    repeat step || t_listutils || simp reducible_values in * || instantiate_any || unfold reduces_to in *;
      t_closer.

  match goal with
  | H: forall a, _ |- _ => unshelve epose proof (H t' _); steps; eauto with berased
  end.

  rewrite open_none in *; auto.
  eexists; repeat step || t_closing; eauto;
    eauto using star_smallstep_trans with bsteplemmas values.
Qed.


Lemma open_reducible_app:
  forall tvars gamma U V t1 t2,
    open_reducible tvars gamma t1 (T_arrow U V) ->
    open_reducible tvars gamma t2 U ->
    open_reducible tvars gamma (app t1 t2) (T_let t2 V).
Proof.
  unfold open_reducible in *; steps;
    eauto using reducible_app.
Qed.

Lemma reducible_app_sem:
  forall theta e u U V T,
    valid_interpretation theta ->
    reducible theta e (T_arrow U V) ->
    reducible_values theta u U ->
    T = open 0 V u ->
    reducible theta (app e u) T.
Proof.
  steps.
  eauto using reducible_let2, reducible_app, reducible_value_expr, red_is_val.
Qed.
