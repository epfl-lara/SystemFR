Require Export SystemFR.ErasedList.

Opaque reducible_values.

Lemma nil_subtype_list:
  forall Θ Γ,
    [ Θ; Γ ⊨ Nil <: List ].
Proof.
  unfold open_subtype, subtype;
    repeat step || rewrite subst_list || simp_red_top_level_hyp.
(*
  eapply reducibility_equivalent; eauto using equivalent_sym;
    repeat step;
    t_closer;
    eauto using is_erased_type_list, wf_list.

  pose proof (open_reducible_nil (support ρ) Γ);
    repeat step || t_instantiate_sat2 || rewrite subst_list in *.

  apply reducible_expr_value; steps.*)
Qed.

Lemma open_subcons_helper:
  forall Θ Γ H T,
    [ Θ; Γ ⊨ Cons H T <: List ].
Proof.
  unfold open_subtype, subtype;
    repeat step || rewrite subst_list || simp_red_top_level_hyp || open_none.
(*
  eapply reducibility_equivalent; eauto using equivalent_sym;
    repeat step;
    t_closer;
    eauto using is_erased_type_list, wf_list.

  apply reducible_values_fold_gen with 0;
    repeat step || simp_spos.

  - simp_red_top_level_hyp; repeat step.

    + apply reducible_expr_value; steps; eauto with values.
      apply reducible_left; steps;
        eauto using reducible_value_expr, reducible_top.

    + apply reducible_expr_value; steps; eauto with values.
      apply reducible_right; steps;
        eauto using reducible_value_expr, reducible_top.

  - apply reducible_expr_value; steps; eauto with values.
    apply reducible_right; steps.
    apply reducible_pp; steps; eauto using reducible_value_expr, reducible_top.
*)
Qed.

Lemma open_subcons:
  forall Γ H T,
    [ Γ ⊨ Cons H T <: List ].
Proof.
  eauto using open_subcons_helper.
Qed.
