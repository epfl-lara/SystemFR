Require Import Equations.Equations.

Require Export SystemFR.RedTactics.

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
  exists (is_pair v); steps; eauto using reducible_values_is_pair.
  eapply star_trans; eauto with cbvlemmas.
  apply star_one.
  constructor;
    eauto using red_is_val;
    eauto using fv_nil_top_level_var with fv.
Qed.

Lemma reducible_is_succ:
  forall theta t,
    valid_interpretation theta ->
    reducible theta t T_top ->
    reducible theta (boolean_recognizer 1 t) T_bool.
Proof.
  unfold reducible, reduces_to; repeat step.
  exists (is_succ v); steps; eauto using reducible_values_is_succ.
  eapply star_trans; eauto with cbvlemmas.
  apply star_one.
  constructor;
    eauto using red_is_val;
    eauto using fv_nil_top_level_var with fv.
Qed.

Lemma reducible_is_lambda:
  forall theta t,
    valid_interpretation theta ->
    reducible theta t T_top ->
    reducible theta (boolean_recognizer 2 t) T_bool.
Proof.
  unfold reducible, reduces_to; repeat step.
  exists (is_lambda v); steps; eauto using reducible_values_is_lambda.
  eapply star_trans; eauto with cbvlemmas.
  apply star_one.
  constructor;
    eauto using red_is_val;
    eauto using fv_nil_top_level_var with fv.
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
