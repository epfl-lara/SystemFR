Require Import List.
Import ListNotations.

Require Export SystemFR.ReducibilityLemmas.
Require Export SystemFR.NatEq.
Require Export SystemFR.EquivalenceLemmas2.

Opaque reducible_values.

Definition computable_equality_with f_eq theta T : Prop :=
  forall v1 v2,
    reducible_values theta v1 T ->
    reducible_values theta v2 T ->
      star scbv_step (app (app f_eq v1) v2) ttrue <->
      equivalent_terms v1 v2.

Definition computable_equality theta T : Prop :=
  exists f_eq,
    wf f_eq 0 /\
    is_erased_term f_eq /\
    pfv f_eq term_var = nil /\
    computable_equality_with f_eq theta T.

Lemma computable_equality_subtype:
  forall theta A B,
    computable_equality theta A ->
    subtype theta B A ->
    computable_equality theta B.
Proof.
  unfold computable_equality, computable_equality_with;
    repeat step;
    eauto with apply_any step_tactic.
Qed.

Lemma computable_equality_prod:
  forall theta A B,
    valid_interpretation theta ->
    wf A 0 ->
    wf B 0 ->
    computable_equality theta A ->
    computable_equality theta B ->
    computable_equality theta (T_prod A B).
Proof.
  unfold computable_equality, computable_equality_with; steps.
  exists (notype_lambda (notype_lambda (
    ite (app (app f_eq0 (pi1 (lvar 1 term_var))) (pi1 (lvar 0 term_var)))
        (app (app f_eq (pi2 (lvar 1 term_var))) (pi2 (lvar 0 term_var)))
        tfalse)));
    repeat step || simp_red || list_utils; eauto with wf.

  - reverse_once; repeat open_none; eauto with values.
    reverse_once; repeat open_none.
    reverse_once; repeat open_none || step; eauto with values.
    apply star_smallstep_value in H39; steps; eauto with values.
    apply star_smallstep_value in H40; steps; eauto with values.
    reverse_once; repeat open_none.
    apply equivalent_pp.
    + apply H10; steps.
      apply equivalent_star_true with (app (app f_eq0 (pi1 (pp a0 b0))) (pi1 (pp v1 v0)));
        repeat apply equivalent_app || step;
        try solve [ apply equivalent_refl; steps ];
        try solve [ apply equivalent_star; steps; t_closer; eauto using star_one with smallstep ].
    + apply H7; steps.
      apply equivalent_star_true with (app (app f_eq (pi2 (pp a0 b0))) (pi2 (pp v1 v0)));
        repeat apply equivalent_app || step;
        try solve [ apply equivalent_refl; steps ];
        try solve [ apply equivalent_star; steps; t_closer; eauto using star_one with smallstep ].

  - one_step.
    one_step.
    apply_anywhere equivalent_value_pair; steps; t_closer.
    apply star_smallstep_ite_true.
    + apply equivalent_star_true with (app (app f_eq0 a0) v1');
        repeat apply equivalent_app || step;
        try solve [ apply equivalent_refl; steps ];
        try solve [ apply equivalent_sym, equivalent_star; steps; t_closer;
                    apply star_one; constructor; t_closer ];
        eauto with apply_any.
    + apply equivalent_star_true with (app (app f_eq b0) v2');
        repeat apply equivalent_app || step;
        try solve [ apply equivalent_refl; steps ];
        try solve [ apply equivalent_sym, equivalent_star; steps; t_closer;
                    apply star_one; constructor; t_closer ];
        eauto with apply_any.
Qed.

Lemma computable_equality_nat:
  computable_equality_with nat_eq_fix [] T_nat.
Proof.
  unfold computable_equality_with; repeat step || simp_red.
  - apply_anywhere nat_eq_sound; steps; t_closer.
    apply equivalent_refl; t_closer.
  - apply_anywhere equivalent_value_nat; steps; eauto with values;
      eauto using nat_eq_complete2.
Qed.
