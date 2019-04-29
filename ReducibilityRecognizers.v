Require Import Equations.Equations.

Require Import SystemFR.Tactics.
Require Import SystemFR.Trees.
Require Import SystemFR.Syntax.
Require Import SystemFR.TermList.
Require Import SystemFR.AssocList.
Require Import SystemFR.StarRelation.
Require Import SystemFR.SmallStep.
Require Import SystemFR.PrimitiveSize.
Require Import SystemFR.StarLemmas.
Require Import SystemFR.PrimitiveRecognizers.

Require Import SystemFR.ReducibilityDefinition.
Require Import SystemFR.ReducibilityLemmas.
Require Import SystemFR.ReducibilityCandidate.
Require Import SystemFR.RedTactics.

Opaque reducible_values.

Lemma reducible_values_is_pair:
  forall theta v,
    reducible_values theta (is_pair v) T_bool.
Proof.
  destruct v; repeat step || simp_red.
Qed.

Lemma reducible_values_is_succ:
  forall theta v,
    reducible_values theta (is_succ v) T_bool.
Proof.
  destruct v; repeat step || simp_red.
Qed.

Lemma reducible_values_is_lambda:
  forall theta v,
    reducible_values theta (is_lambda v) T_bool.
Proof.
  destruct v; repeat step || simp_red.
Qed.

Lemma reducible_is_pair:
  forall theta t,
    valid_interpretation theta ->
    reducible theta t T_top ->
    reducible theta (boolean_recognizer 0 t) T_bool.
Proof.
  unfold reducible, reduces_to; repeat step.
  exists (is_pair t'); steps; eauto using reducible_values_is_pair.
  eauto 7 using star_smallstep_trans, red_is_val with bsteplemmas smallstep bfv.
Qed.

Lemma reducible_is_succ:
  forall theta t,
    valid_interpretation theta ->
    reducible theta t T_top ->
    reducible theta (boolean_recognizer 1 t) T_bool.
Proof.
  unfold reducible, reduces_to; repeat step.
  exists (is_succ t'); steps; eauto using reducible_values_is_succ.
  eauto 7 using star_smallstep_trans, red_is_val with bsteplemmas smallstep bfv.
Qed.

Lemma reducible_is_lambda:
  forall theta t,
    valid_interpretation theta ->
    reducible theta t T_top ->
    reducible theta (boolean_recognizer 2 t) T_bool.
Proof.
  unfold reducible, reduces_to; repeat step.
  exists (is_lambda t'); steps; eauto using reducible_values_is_lambda.
  eauto 7 using star_smallstep_trans, red_is_val with bsteplemmas smallstep bfv.
Qed.

Lemma open_reducible_is_pair:
  forall tvars gamma t,
    open_reducible tvars gamma t T_top ->
    open_reducible tvars gamma (boolean_recognizer 0 t) T_bool.
Proof.
  unfold open_reducible; steps; eauto using reducible_is_pair.
Qed.

Lemma open_reducible_is_succ:
  forall tvars gamma t,
    open_reducible tvars gamma t T_top ->
    open_reducible tvars gamma (boolean_recognizer 1 t) T_bool.
Proof.
  unfold open_reducible; steps; eauto using reducible_is_succ.
Qed.

Lemma open_reducible_is_lambda:
  forall tvars gamma t,
    open_reducible tvars gamma t T_top ->
    open_reducible tvars gamma (boolean_recognizer 2 t) T_bool.
Proof.
  unfold open_reducible; steps; eauto using reducible_is_lambda.
Qed.
