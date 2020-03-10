Require Import List.
Import ListNotations.

Require Export SystemFR.ErasedArrow.
Require Export SystemFR.ErasedBool.
Require Export SystemFR.ErasedPair.
Require Export SystemFR.NatEq.
Require Export SystemFR.EquivalenceLemmas2.

Opaque reducible_values.

Definition computable_equality_with f_eq theta T : Prop :=
  wf f_eq 0 /\
  is_erased_term f_eq /\
  pfv f_eq term_var = nil /\
  reducible theta f_eq (T_arrow T (T_arrow T T_bool)) /\
  forall v1 v2,
    reducible_values theta v1 T ->
    reducible_values theta v2 T ->
      star scbv_step (app (app f_eq v1) v2) ttrue <->
      equivalent_terms v1 v2.

Definition computable_equality theta T : Prop :=
  exists f_eq,
    computable_equality_with f_eq theta T.

Lemma computable_equality_subtype:
  forall theta A B,
    computable_equality theta A ->
    valid_interpretation theta ->
    subtype theta B A ->
    is_erased_type B ->
    wf A 0 ->
    wf B 0 ->
    computable_equality theta B.
Proof.
  unfold computable_equality, computable_equality_with;
    repeat step.

  eexists; steps;
    eauto with apply_any.

  eapply reducible_values_exprs; try eassumption;
    repeat step || simp_red || apply_any || open_none.

  repeat unfold reduces_to in *; steps; t_closer.

  unshelve epose proof (H13 a _ _ _ _); repeat step || open_none.
  exists v; repeat step || simp_red.
Qed.

Lemma computable_equality_prod:
  forall theta A B,
    valid_interpretation theta ->
    wf A 0 ->
    wf B 0 ->
    is_erased_type A ->
    is_erased_type B ->
    pfv A term_var = nil ->
    pfv B term_var = nil ->
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

  - apply reducible_value_expr; auto.
    apply reducible_lambda; repeat step || list_utils || open_none; t_closer.
    apply reducible_value_expr; auto.
    apply reducible_lambda; repeat step || list_utils || open_none; t_closer.

    apply reducible_ite; repeat step; t_closer;
      eauto using reducible_value_expr, reducible_false.
    + apply reducible_app2 with A; steps; eauto using reducible_value_expr, reducible_pi1.
      apply reducible_app2 with A; steps; eauto using reducible_value_expr, reducible_pi1.
    + apply reducible_app2 with B; steps; eauto using reducible_value_expr, reducible_pi2_nodep.
      apply reducible_app2 with B; steps; eauto using reducible_value_expr, reducible_pi2_nodep.

  - reverse_once; repeat open_none; eauto with values.
    reverse_once; repeat open_none.
    reverse_once; repeat open_none || step; eauto with values.
    apply star_smallstep_value in H45; steps; eauto with values.
    apply star_smallstep_value in H46; steps; eauto with values.
    reverse_once; repeat open_none.
    apply equivalent_pp.
    + apply H16; steps.
      apply equivalent_star_true with (app (app f_eq0 (pi1 (pp a0 b0))) (pi1 (pp v1 v0)));
        repeat apply equivalent_app || step;
        try solve [ apply equivalent_refl; steps ];
        try solve [ apply equivalent_star; steps; t_closer; eauto using star_one with smallstep ].
    + apply H12; steps.
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

Lemma computable_equality_with_nat_eq:
  computable_equality_with nat_eq_fix [] T_nat.
Proof.
  unfold computable_equality_with; repeat step || simp_red; eauto with lia.
  - unfold nat_eq_fix.
    eapply backstep_reducible; steps; eauto with lia; eauto with smallstep;
      repeat step.

    apply reducible_value_expr; steps.
    apply reducible_lambda; steps; eauto with lia.
    apply reducible_value_expr; steps.
    assert (valid_interpretation []); steps.
    apply reducible_lambda; repeat step || simp_red || list_utils || open_none; eauto with lia; t_closer.

    apply star_smallstep_reducible with (nat_eq u u0);
      repeat step || unfold reducible, reduces_to;
      try solve [
        unfold nat_eq, nat_eq_fix, closed_term; repeat step || list_utils; eauto with lia; t_closer
      ].

    + unfold nat_eq, nat_eq_fix.
      one_step; steps.
      one_step; steps.
      one_step; steps.
    + unshelve epose proof (nat_eq_bool u _ u0 _); steps;
        try solve [ eexists; steps; try eassumption; repeat step || simp_red ].

  - apply_anywhere nat_eq_sound; steps; t_closer.
    apply equivalent_refl; t_closer.
  - apply_anywhere equivalent_value_nat; steps; eauto with values;
      eauto using nat_eq_complete2.
Qed.

Lemma computable_equality_nat:
  computable_equality [] T_nat.
Proof.
  unfold computable_equality;
    eauto using computable_equality_with_nat_eq.
Qed.
