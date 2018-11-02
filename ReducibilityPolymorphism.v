Require Import Coq.Lists.List.

Require Import Termination.Sets.
Require Import Termination.Tactics.
Require Import Termination.Syntax.
Require Import Termination.TermList.
Require Import Termination.SmallStep.
Require Import Termination.AssocList.
Require Import Termination.EquivalenceLemmas.
Require Import Termination.ListUtils.
Require Import Termination.SubstitutionLemmas.
Require Import Termination.StarRelation.
Require Import Termination.SizeLemmas.
Require Import Termination.StarLemmas.
Require Import Termination.TypeErasure.
Require Import Termination.SubstitutionErase.
Require Import Termination.TreeLists.
Require Import Termination.TermListReducible.

Require Import Termination.ReducibilityCandidate.
Require Import Termination.ReducibilityDefinition.
Require Import Termination.ReducibilityLemmas.
Require Import Termination.ReducibilityRenaming.
Require Import Termination.ReducibilityUnused.
Require Import Termination.ReducibilitySubst.
Require Import Termination.RedTactics.

Require Import Termination.Freshness.

Require Import Termination.FVLemmasLists.
Require Import Termination.WFLemmasLists.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducible_type_abs_value:
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
    reducible_values theta (type_abs t) (T_abs T).
Proof.
  repeat step || simp_red;
    eauto with bfv;
    eauto with bwf.
  exists X; repeat step || rewrite reducibility_rewrite.
  apply backstep_reducible with t; repeat step || t_listutils;
    eauto 2 using reducible_value_expr with step_tactic.
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
    reducible theta (type_abs t) (T_abs T).
Proof.
  intros; eauto using reducible_type_abs_value, reducible_value_expr.
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
    open_reducible tvars gamma (type_abs t) (T_abs T).
Proof.
  unfold open_reducible; repeat step || t_termlist.

  apply reducible_type_abs with X;
    repeat step || rewrite fv_subst_different_tag in * by (steps; eauto with bfv);
      eauto with bwf;
      eauto with bfv;
      eauto with berased.

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
    valid_interpretation theta ->
    is_erased_type U ->
    reducible theta t (T_abs U) ->
    reducible theta (notype_inst t) (topen 0 U V).
Proof.
  unfold reducible, reduces_to in *;
    repeat step || t_listutils || simp_red || unfold reduces_to in *.
  match goal with
  | H: forall RC, reducibility_candidate RC -> _ |- _ =>
      unshelve epose proof (H (fun v => reducible_values theta v V) _); steps;
        eauto using reducibility_is_candidate
  end.
  exists t'0; steps; eauto using star_smallstep_trans with bsteplemmas.
  apply (reducible_rename_one _ _ _ _ _ (makeFresh (pfv U type_var :: pfv V type_var :: nil))) in H20;
    repeat step || finisher; eauto using reducibility_is_candidate.
  eapply reducibility_subst_head; eauto; repeat step || t_listutils || finisher.
Qed.

Lemma open_reducible_inst:
  forall tvars (gamma : context) t U V,
    wf V 0 ->
    twf V 0 ->
    is_erased_type U ->
    subset (fv V) (support gamma) ->
    open_reducible tvars gamma t (T_abs U) ->
    open_reducible tvars gamma (notype_inst t) (topen 0 U V).
Proof.
  unfold open_reducible;
    repeat step || t_instantiate_sat3 || rewrite substitute_topen || apply reducible_inst ||
      rewrite fv_subst_different_tag in * by (steps; eauto with bfv);
    eauto with bwf;
    eauto with btwf;
    eauto with bfv;
    eauto with berased.
Qed.
