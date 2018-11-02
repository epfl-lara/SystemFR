Require Import Equations.Equations.
Require Import Coq.Lists.List.

Require Import Termination.Syntax.
Require Import Termination.Tactics.
Require Import Termination.ListUtils.
Require Import Termination.Sets.
Require Import Termination.AssocList.
Require Import Termination.Freshness.
Require Import Termination.SubstitutionLemmas.
Require Import Termination.TermList.
Require Import Termination.StarLemmas.
Require Import Termination.SetLemmas.
Require Import Termination.TermForm.
Require Import Termination.StarRelation.
Require Import Termination.SmallStep.

Require Import Termination.ReducibilityDefinition.
Require Import Termination.ReducibilityLemmas.
Require Import Termination.ReducibilityLetRules.
Require Import Termination.RedTactics.

Require Import Termination.WFLemmas.
Require Import Termination.WFLemmasLists.

Require Import Termination.FVLemmas.
Require Import Termination.FVLemmasLists.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducible_lambda:
  forall theta t U V,
    wf U 0 ->
    wf t 1 ->
    fv U = nil ->
    fv t = nil ->
    valid_interpretation theta ->
    (forall u, reducible_values theta u U -> reducible theta (open 0 t u) (T_let u U V)) ->
    reducible_values theta (lambda U t) (T_arrow U V).
Proof.
  repeat step || t_listutils || simp reducible_values in * || rewrite reducibility_rewrite;
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
    open_reducible tvars ((x, U) :: gamma) (open 0 t (fvar x)) (open 0 V (fvar x)) ->
    open_reducible tvars gamma (lambda U t) (T_arrow U V).
Proof.
  unfold open_reducible in *; steps.

  apply reducible_value_expr; steps.
  apply reducible_lambda; steps;
    eauto with bwf;
    eauto with bfv sets btermlist;
    eauto 2 with btf.
  
  - unshelve epose proof (H7 theta ((x,u) :: lterms) _ _ _); repeat tac1 || t_sets;
      eauto using reducible_let with btf.
Qed.

Lemma reducible_app:
  forall theta U V t1 t2,
    valid_interpretation theta ->
    reducible theta t1 (T_arrow U V) ->
    reducible theta t2 U ->
    reducible theta (app t1 t2) (T_let t2 U V).
Proof.
  intros U V t1 t2 H1 H2.
  unfold reducible, reduces_to in *;
    repeat step || t_listutils || simp reducible_values in * || unfold reduces_to in *.

  unshelve epose proof (H12 t' _); steps; eauto with btf.
  exists t'1; repeat step || simp reducible_values in *;
    eauto using star_smallstep_trans with bsteplemmas values.
  exists t'; repeat step || simp reducible_values in *; eauto using red_is_val; eauto with btf.
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
    repeat step || t_listutils || simp reducible_values in * || unfold reduces_to in *.

  unshelve epose proof (H12 t' _ _); steps; eauto with btf.
  rewrite open_none in *; auto.
  eexists; steps; eauto;
    eauto using star_smallstep_trans with bsteplemmas values.
Qed.


Lemma open_reducible_app:
  forall tvars gamma U V t1 t2,
    open_reducible tvars gamma t1 (T_arrow U V) ->
    open_reducible tvars gamma t2 U ->
    open_reducible tvars gamma (app t1 t2) (T_let t2 U V).
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
