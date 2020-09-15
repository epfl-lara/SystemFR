Require Export SystemFR.TypedEquality.
Require Export SystemFR.ErasedArrow.

Opaque T_equivalent_at.
Opaque reducible_values.

Lemma fun_apply:
  forall theta A B f1 f2 a1 a2,
    valid_interpretation theta ->
    wf A 0 ->
    wf B 0 ->
    twf B 0 ->
    pfv A term_var = nil ->
    pfv B term_var = nil ->
    equivalent_at theta A a1 a2 ->
    equivalent_at theta (T_arrow A B) f1 f2 ->
    equivalent_at theta B (app f1 a1) (app f2 a2).
Proof.
  unfold equivalent_at; steps;
    eauto using reducible_app2, reducible_value_expr.

  unshelve epose proof (H11 (notype_lambda (app f (app (lvar 0 term_var) a1))) _ _ _ _);
    repeat step || apply reducible_lambda || list_utils ||
           (rewrite open_none in * by t_closer);
    t_closer.

  - apply reducible_app2 with B;
      repeat step;
      eauto using reducible_value_expr with step_tactic;
      eauto using reducible_app2, reducible_value_expr.

  - eapply equivalent_square; eauto.
    + eapply equivalent_trans.
      * unfold reducible, reduces_to in H5; steps.
        apply equivalent_beta with v; steps; t_closer.
      * repeat step || rewrite open_none in * by t_closer.
        apply equivalent_refl; repeat step || list_utils; eauto with wf erased fv.
    + eapply equivalent_trans.
      * unfold reducible, reduces_to in H8; steps.
        apply equivalent_beta with v; steps; t_closer.
      * repeat step || rewrite open_none in * by t_closer.

        unshelve epose proof (H10 (notype_lambda (app f (app f2 (lvar 0 term_var))))
                                 _ _ _ _);
          repeat step || apply reducible_lambda || (rewrite open_none in * by t_closer);
          t_closer;
          try finisher.

        -- apply reducible_app2 with B;
             repeat step;
             eauto using reducible_value_expr with step_tactic;
             eauto using reducible_app2, reducible_value_expr.

        -- apply (equivalent_square _ _ _ _ H16); eauto.
          ++ eapply equivalent_trans.
            ** unfold reducible, reduces_to in *; repeat step.
               eapply equivalent_beta; eauto;
                 repeat step || list_utils;
                 try solve [ t_closer ].
            ** repeat step || (rewrite open_none in * by t_closer).
               apply equivalent_refl; steps; t_closer.
          ++ eapply equivalent_trans.
            ** unfold reducible, reduces_to in *; repeat step.
               eapply equivalent_beta; eauto;
                 repeat step || list_utils;
                 try solve [ t_closer ].
            ** repeat step || (rewrite open_none in * by t_closer).
               apply equivalent_refl; steps; t_closer.
Qed.

Lemma open_equivalent_fun_apply:
  forall tvars gamma A B a1 a2 f1 f2 p p',
    wf A 0 ->
    wf B 0 ->
    twf A 0 ->
    twf B 0 ->
    subset (fv A) (support gamma) ->
    subset (fv B) (support gamma) ->
    is_erased_type A ->
    is_erased_type B ->
    is_erased_term a1 ->
    is_erased_term a2 ->
    is_erased_term f1 ->
    is_erased_term f2 ->
    wf a1 0 ->
    wf a2 0 ->
    wf f1 0 ->
    wf f2 0 ->
    pfv a1 term_var = nil ->
    pfv a2 term_var = nil ->
    pfv f1 term_var = nil ->
    pfv f2 term_var = nil ->
    [ tvars; gamma ⊨ p : T_equivalent_at (T_arrow A B) f1 f2 ] ->
    [ tvars; gamma ⊨ p': T_equivalent_at A a1 a2 ] ->
    [ tvars; gamma ⊨ uu: T_equivalent_at B (app f1 a1) (app f2 a2) ].
Proof.
  unfold open_reducible;
    repeat step || t_instantiate_sat3 || rewrite subst_equivalent_at in *.

  apply_anywhere equivalent_at_type_prop2;
    repeat step;
    t_closer.

  apply_anywhere equivalent_at_type_prop2;
    repeat step;
    t_closer.

  apply reducible_value_expr; steps.
  apply equivalent_at_prop_type;
    repeat step;
    t_closer.

  apply fun_apply with (psubstitute A lterms term_var); eauto;
    repeat step;
    t_closer.
Qed.

Lemma open_equivalent_at_equivalent:
  forall tvars gamma t1 t2 A,
    is_erased_type A ->
    is_erased_term t1 ->
    is_erased_term t2 ->
    wf A 0 ->
    wf t1 0 ->
    wf t2 0 ->
    twf A 0 ->
    [ tvars; gamma ⊨ t1 : A ] ->
    [ tvars; gamma ⊨ t2 : A ] ->
    [ tvars; gamma ⊨ t1 ≡ t2 ] ->
    [ tvars; gamma ⊨ uu: T_equivalent_at A t1 t2 ].
Proof.
  unfold open_reducible, open_equivalent;
    repeat step || t_instantiate_sat3 || rewrite subst_equivalent_at ||
           apply reducible_value_expr ||
           apply equivalent_app ||
           apply equivalent_at_prop_type || unfold equivalent_at;
    try solve [ t_closer ];
    try solve [ apply equivalent_refl; auto ].
Qed.

(*
Lemma fun_ext:
  forall theta A B f1 f2,
    valid_interpretation theta ->
    reducible theta f1 (T_arrow A B) ->
    reducible theta f2 (T_arrow A B) ->
    (forall a,
      equivalent_at theta B (app f1 a) (app f2 a)) ->
    equivalent_at theta (T_arrow A B) f1 f2.
Proof.
  intros; unfold equivalent_at; steps.
Admitted.

Lemma open_reducible_fun_ext:
  forall tvars gamma A B f1 f2 p x,
    [ tvars; gamma ⊨ f1 : T_arrow A B ] ->
    [ tvars; gamma ⊨ f2 : T_arrow A B ] ->
    [ tvars; (x, A) :: gamma ⊨ p: T_equivalent_at B
                                   (app f1 (fvar x term_var))
                                   (app f2 (fvar x term_var)) ] ->
    [ tvars; gamma ⊨ uu: T_equivalent_at (T_arrow A B) f1 f2 ].
Proof.
Admitted.
*)
