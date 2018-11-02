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
Require Import Termination.TypeForm.

Require Import Termination.Equivalence.
Require Import Termination.EquivalenceLemmas.

Require Import Termination.FVLemmas.
Require Import Termination.FVLemmasTermList.

Require Import Termination.WFLemmas.
Require Import Termination.WFLemmasTermList.

Require Import Termination.ReducibilityDefinition.
Require Import Termination.ReducibilityLemmas.
Require Import Termination.ReducibilityLetRules.
Require Import Termination.RedTactics.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducible_values_pp:
  forall v1 v2 T1 T2,
    reducible_values v1 T1 ->
    reducible_values v2 (open 0 T2 v1) ->
    reducible_values (pp v1 v2) (T_prod T1 T2).
Proof.
  repeat step || simp reducible_values || rewrite reducibility_rewrite;
    eauto with btf step_tactic.
Qed.

Lemma reducible_pp:
  forall U V t1 t2,
    reducible t1 U ->
    reducible t2 (T_let t1 U V) ->
    reducible (pp t1 t2) (T_prod U V).
Proof.
  unfold reducible, reduces_to; repeat step || t_listutils.
  exists (pp t'0 t'); repeat step || simp_red || t_values_info2 || t_deterministic_star;
    eauto 6 using red_is_val with bsteplemmas.
Qed.

Lemma open_reducible_pp:
  forall gamma U V t1 t2,
    open_reducible gamma t1 U ->
    open_reducible gamma t2 (T_let t1 U V) ->
    open_reducible gamma (pp t1 t2) (T_prod U V).
Proof.
  unfold open_reducible in *; steps; eauto using reducible_pp.
Qed.

Lemma reducible_values_pi1:
  forall U V t,
    reducible_values t (T_prod U V) ->
    reducible (pi1 t) U.
Proof.
  repeat step || t_values_info2 || simp reducible_values in *.
  eapply backstep_reducible; repeat step || t_listutils;
    eauto with smallstep;
    eauto with bfv bwf;
    eauto using reducible_value_expr.
Qed.

Lemma reducible_pi1:
  forall U V t,
    reducible t (T_prod U V) ->
    reducible (pi1 t) U.
Proof.
  intros U V t H.
  unfold reducible, reduces_to in H; steps.
  eapply star_backstep_reducible;
    eauto with bsteplemmas;
    eauto using reducible_values_pi1.
Qed.

Lemma open_reducible_pi1:
  forall gamma U V t,
    open_reducible gamma t (T_prod U V) ->
    open_reducible gamma (pi1 t) U.
Proof.
  unfold open_reducible in *; steps; eauto using reducible_pi1.
Qed.

Lemma reducible_values_pi2:
  forall U V t,
    reducible_values t (T_prod U V) ->
    reducible (pi2 t) (T_let (pi1 t) U V).
Proof.  
  repeat step || t_values_info2 || simp reducible_values in *.
  eapply backstep_reducible; repeat step || t_listutils || simp reducible_values in *;
    eauto with smallstep;
    eauto with bfv bwf;
    eauto using reducible_value_expr.

  apply reducible_let_backstep_expr with a;
    eauto with smallstep.
  
  apply reducible_let; eauto using reducible_value_expr.
Qed.

Lemma reducible_pi2:
  forall U V t,
    reducible t (T_prod U V) ->
    reducible (pi2 t) (T_let (pi1 t) U V).
Proof.
  intros U V t H.
  unfold reducible, reduces_to in H; steps.
  eapply star_backstep_reducible; eauto with bsteplemmas.
  eapply reducible_let_backstep_expr; eauto with bsteplemmas.
  eauto using reducible_values_pi2.
Qed.

Lemma open_reducible_pi2:
  forall gamma U V t,
    open_reducible gamma t (T_prod U V) ->
    open_reducible gamma (pi2 t) (T_let (pi1 t) U V).
Proof.
  unfold open_reducible in *; steps; eauto using reducible_pi2.
Qed.

Lemma reducible_unit:
  reducible uu T_unit.
Proof.
  unfold reducible, reduces_to;
    repeat step; eauto with step_tactic smallstep.
Qed.

Lemma open_reducible_unit:
  forall gamma,
    open_reducible gamma uu T_unit.
Proof.
  unfold open_reducible in *; repeat step;
    auto using reducible_unit.
Qed.
