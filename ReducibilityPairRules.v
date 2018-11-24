Require Import Equations.Equations.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Require Import Termination.Syntax.
Require Import Termination.Tactics.
Require Import Termination.TermProperties.
Require Import Termination.Sets.
Require Import Termination.TermList.
Require Import Termination.ListUtils.
Require Import Termination.AssocList.
Require Import Termination.Freshness.
Require Import Termination.SmallStep.
Require Import Termination.SubstitutionLemmas.
Require Import Termination.StarLemmas.
Require Import Termination.StarInversions.
Require Import Termination.SmallStepSubstitutions.
Require Import Termination.SubstitutionErase.
Require Import Termination.TreeLists.
Require Import Termination.TermListReducible.
Require Import Termination.TypeErasureLemmas.

Require Import Termination.Equivalence.
Require Import Termination.EquivalenceLemmas.

Require Import Termination.FVLemmas.
Require Import Termination.FVLemmasLists.

Require Import Termination.WFLemmas.
Require Import Termination.WFLemmasLists.

Require Import Termination.ReducibilityCandidate.
Require Import Termination.ReducibilityDefinition.
Require Import Termination.ReducibilityLemmas.
Require Import Termination.ReducibilityLetRules.
Require Import Termination.RedTactics.

Opaque reducible_values.
Opaque makeFresh.

Set Program Mode.

Lemma reducible_values_pp:
  forall theta v1 v2 T1 T2,
    valid_interpretation theta ->
    reducible_values theta v1 T1 ->
    reducible_values theta v2 (open 0 T2 v1) ->
    reducible_values theta (pp v1 v2) (T_prod T1 T2).
Proof.
  repeat step || simp reducible_values || t_closer ||
         rewrite reducibility_rewrite || unshelve exists v1, v2;
    eauto with berased;
    eauto with bfv;
    eauto with bwf;
    eauto with values.
Qed.

Lemma reducible_pp:
  forall theta U V t1 t2,
    valid_interpretation theta ->
    reducible theta t1 U ->
    reducible theta t2 (T_let t1 U V) ->
    reducible theta (pp t1 t2) (T_prod U V).
Proof.
  unfold reducible, reduces_to; repeat step || t_listutils; try t_closer.
  exists (pp t'0 t'); repeat step || simp_red || t_values_info2 || t_deterministic_star;
    eauto 6 using red_is_val with bsteplemmas;
    try t_closer.
Qed.

Lemma open_reducible_pp:
  forall tvars gamma U V t1 t2,
    open_reducible tvars gamma t1 U ->
    open_reducible tvars gamma t2 (T_let t1 U V) ->
    open_reducible tvars gamma (pp t1 t2) (T_prod U V).
Proof.
  unfold open_reducible in *; steps; eauto using reducible_pp.
Qed.

Lemma reducible_values_pi1:
  forall theta U V t,
    valid_interpretation theta ->
    reducible_values theta t (T_prod U V) ->
    reducible theta (pi1 t) U.
Proof.
  repeat step || t_values_info2 || simp reducible_values in *.
  eapply backstep_reducible; repeat step || t_listutils;
    eauto with smallstep;
    eauto with bfv bwf;
    eauto using reducible_value_expr;
    eauto with berased.
Qed.

Lemma reducible_pi1:
  forall theta U V t,
    valid_interpretation theta ->
    reducible theta t (T_prod U V) ->
    reducible theta (pi1 t) U.
Proof.
  intros theta U V t HV H.
  unfold reducible, reduces_to in H; steps.
  eapply star_backstep_reducible; steps;
    eauto with bsteplemmas;
    eauto using reducible_values_pi1;
    try t_closer.
Qed.

Lemma open_reducible_pi1:
  forall tvars gamma U V t,
    open_reducible tvars gamma t (T_prod U V) ->
    open_reducible tvars gamma (pi1 t) U.
Proof.
  unfold open_reducible in *; steps; eauto using reducible_pi1.
Qed.

Lemma reducible_values_pi2:
  forall theta U V t,
    valid_interpretation theta ->
    reducible_values theta t (T_prod U V) ->
    reducible theta (pi2 t) (T_let (pi1 t) U V).
Proof.
  repeat step || t_values_info2 || simp reducible_values in *.
  eapply backstep_reducible; repeat step || t_listutils || simp reducible_values in *;
    eauto with smallstep;
    eauto with bfv bwf;
    eauto using reducible_value_expr;
    eauto with berased.

  apply reducible_let_backstep_expr with a; steps;
    eauto with smallstep;
    eauto with berased.

  apply reducible_let; eauto using reducible_value_expr.
Qed.

Lemma reducible_pi2:
  forall theta U V t,
    valid_interpretation theta ->
    reducible theta t (T_prod U V) ->
    reducible theta (pi2 t) (T_let (pi1 t) U V).
Proof.
  intros theta U V t HV H.
  unfold reducible, reduces_to in H; steps.
  eapply star_backstep_reducible; eauto with bsteplemmas; t_closer.
  eapply reducible_let_backstep_expr; eauto with bsteplemmas; t_closer.
  eauto using reducible_values_pi2.
Qed.

Lemma open_reducible_pi2:
  forall tvars gamma U V t,
    open_reducible tvars gamma t (T_prod U V) ->
    open_reducible tvars gamma (pi2 t) (T_let (pi1 t) U V).
Proof.
  unfold open_reducible in *; steps; eauto using reducible_pi2.
Qed.

Lemma reducible_unit:
  forall theta, reducible theta uu T_unit.
Proof.
  repeat step || simp_red || unfold reducible, reduces_to || eexists;
    eauto with smallstep step_tactic.
Qed.

Lemma open_reducible_unit:
  forall theta gamma,
    open_reducible theta gamma uu T_unit.
Proof.
  unfold open_reducible in *; repeat step;
    auto using reducible_unit.
Qed.
