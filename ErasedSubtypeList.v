Require Export SystemFR.ErasedList.

Opaque reducible_values.

Ltac simp_red2 :=
  rewrite reducible_values_equation_1 in * |- ||
  rewrite reducible_values_equation_2 in * |- ||
  rewrite reducible_values_equation_3 in * |- ||
  rewrite reducible_values_equation_4 in * |- ||
  rewrite reducible_values_equation_5 in * |- ||
  rewrite reducible_values_equation_6 in * |- ||
  rewrite reducible_values_equation_7 in * |- ||
  rewrite reducible_values_equation_8 in * |- ||
  rewrite reducible_values_equation_9 in * |- ||
  rewrite reducible_values_equation_10 in * |- ||
  rewrite reducible_values_equation_11 in * |- ||
  rewrite reducible_values_equation_12 in * |- ||
  rewrite reducible_values_equation_13 in * |- ||
  rewrite reducible_values_equation_14 in * |- ||
  rewrite reducible_values_equation_15 in * |- ||
  rewrite reducible_values_equation_16 in * |- ||
  rewrite reducible_values_equation_17 in * |- ||
  rewrite reducible_values_equation_18 in * |- ||
  rewrite reducible_values_equation_19 in * |- ||
  rewrite reducible_values_equation_20 in * |- ||
  rewrite reducible_values_equation_21 in * |- ||
  rewrite reducible_values_equation_22 in * |- ||
  rewrite reducible_values_equation_23 in * |- ||
  rewrite reducible_values_equation_24 in * |- ||
  rewrite reducible_values_equation_25 in * |- ||
  rewrite reducible_values_equation_26 in * |- ||
  rewrite reducible_values_equation_27 in * |- ||
  rewrite reducible_values_equation_28 in * |- ||
  rewrite reducible_values_equation_29 in * |- ||
  rewrite reducible_values_equation_30 in * |- ||
  rewrite reducible_values_equation_31 in * |- ||
  rewrite reducible_values_equation_32 in * |- ||
  rewrite reducible_values_equation_33 in * |- ||
  rewrite reducible_values_equation_34 in * |- ||
  rewrite reducible_values_equation_35 in * |- ||
  rewrite reducible_values_equation_36 in * |- ||
  rewrite reducible_values_equation_37 in * |- ||
  rewrite reducible_values_equation_38 in * |- ||
  rewrite reducible_values_equation_39 in * |- ||
  rewrite reducible_values_equation_40 in * |- ||
  rewrite reducible_values_equation_41 in * |- ||
  rewrite reducible_values_equation_42 in * |- ||
  rewrite reducible_values_equation_43 in * |- ||
  rewrite reducible_values_equation_44 in * |- ||
  rewrite reducible_values_equation_45 in * |- ||
  rewrite reducible_values_equation_46 in * |- ||
  rewrite reducible_values_equation_47 in * |- ||
  rewrite reducible_values_equation_48 in * |- ||
  rewrite reducible_values_equation_49 in * |- ||
  rewrite reducible_values_equation_50 in * |- ||
  rewrite reducible_values_equation_51 in * |- ||
  rewrite reducible_values_equation_52 in * |- ||
  rewrite reducible_values_equation_53 in * |- ||
  rewrite reducible_values_equation_54 in * |- ||
  rewrite reducible_values_equation_55 in * |- ||
  rewrite reducible_values_equation_56 in * |- ||
  rewrite reducible_values_equation_57 in *.

Lemma subst_list:
  forall l tag,
    psubstitute List l tag = List.
Proof.
  steps.
Qed.

Lemma is_erased_type_list:
  is_erased_type List.
Proof.
  steps.
Qed.

Lemma wf_list:
  wf List 0.
Proof.
  steps.
Qed.

Lemma nil_subtype_list:
  forall tvars gamma,
    [ tvars; gamma ⊨ Nil <: List ].
Proof.
  unfold subtype;
    repeat step || rewrite subst_list || simp_red2.

  eapply reducibility_equivalent; eauto using equivalent_sym;
    repeat step;
    t_closer;
    eauto using is_erased_type_list, wf_list.

  pose proof (open_reducible_nil (support theta) gamma);
    repeat step || t_instantiate_sat2 || rewrite subst_list in *.

  apply reducible_expr_value; steps.
Qed.

Lemma cons_subtype_list:
  forall tvars gamma H T,
    wf H 0 ->
    wf T 0 ->
    [ tvars; gamma ⊨ T <: List ] ->
    [ tvars; gamma ⊨ Cons H T <: List ].
Proof.
  unfold subtype;
    repeat step || rewrite subst_list || simp_red2.

  rewrite (open_none _ 1) in H12 by eauto with wf.
  repeat (rewrite open_none in * by t_closer).

  eapply reducibility_equivalent; eauto using equivalent_sym;
    repeat step;
    t_closer;
    eauto using is_erased_type_list, wf_list.

  apply reducible_values_fold_gen with 0;
    repeat step || simp_spos.

  simp_red2;
    repeat step.

  - apply reducible_expr_value; steps; eauto with values.
    apply reducible_left; steps;
      eauto using reducible_value_expr, reducible_top.

  - apply reducible_expr_value; steps; eauto with values.
    apply reducible_right; steps;
      eauto using reducible_value_expr, reducible_top.

  - apply reducible_expr_value; steps; eauto with values.
    apply reducible_right; steps.
    apply reducible_pp; steps; eauto using reducible_value_expr, reducible_top.
Qed.
