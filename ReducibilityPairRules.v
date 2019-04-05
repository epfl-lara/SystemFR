Require Import Equations.Equations.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Require Import SystemFR.Syntax.
Require Import SystemFR.Tactics.
Require Import SystemFR.TermProperties.
Require Import SystemFR.Sets.
Require Import SystemFR.TermList.
Require Import SystemFR.ListUtils.
Require Import SystemFR.AssocList.
Require Import SystemFR.Freshness.
Require Import SystemFR.SmallStep.
Require Import SystemFR.SubstitutionLemmas.
Require Import SystemFR.StarLemmas.
Require Import SystemFR.StarInversions.
Require Import SystemFR.SmallStepSubstitutions.
Require Import SystemFR.SubstitutionErase.
Require Import SystemFR.TreeLists.
Require Import SystemFR.TermListReducible.

Require Import SystemFR.Equivalence.
Require Import SystemFR.EquivalenceLemmas.

Require Import SystemFR.FVLemmas.
Require Import SystemFR.FVLemmasLists.

Require Import SystemFR.WFLemmas.
Require Import SystemFR.WFLemmasLists.

Require Import SystemFR.ReducibilityCandidate.
Require Import SystemFR.ReducibilityDefinition.
Require Import SystemFR.ReducibilityLemmas.
Require Import SystemFR.ReducibilityLetRules.
Require Import SystemFR.RedTactics.

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
    reducible theta t2 (T_let t1 V) ->
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
    open_reducible tvars gamma t2 (T_let t1 V) ->
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
    reducible theta (pi2 t) (T_let (pi1 t) V).
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

  eapply reducible_let; eauto using reducible_value_expr.
Qed.

Lemma reducible_pi2:
  forall theta U V t,
    valid_interpretation theta ->
    reducible theta t (T_prod U V) ->
    reducible theta (pi2 t) (T_let (pi1 t) V).
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
    open_reducible tvars gamma (pi2 t) (T_let (pi1 t) V).
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
