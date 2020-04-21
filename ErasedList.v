Require Export SystemFR.TypeSugar2.
Require Export SystemFR.ErasedRecGen.
Require Export SystemFR.ErasedSum.
Require Export SystemFR.ErasedPair.
Require Export SystemFR.ErasedTop.
Require Export SystemFR.ErasedTypeRefine.

Opaque strictly_positive.
Opaque reducible_values.

Lemma open_reducible_nil:
  forall tvars gamma,
    [ tvars; gamma ⊨ tnil : List ].
Proof.
  intros.

  apply open_reducible_fold_gen2 with 0;
    repeat step || simp_spos;
    eauto with sets.

  apply open_reducible_left.
  apply open_reducible_unit.
Qed.

Lemma open_reducible_singleton:
  forall tvars gamma t T,
    is_erased_term t ->
    wf t 0 ->
    subset (fv t) (support gamma) ->
    [ tvars; gamma ⊨ t : T ] ->
    [ tvars; gamma ⊨ t : tsingleton T t ].
Proof.
  intros.
  unfold tsingleton.
  apply open_reducible_type_refine with uu;
    repeat step || rewrite pfv_shift2 ||
           unfold open_reducible ||
           simp_red ||
           apply reducible_value_expr ||
           (rewrite shift_nothing2 by auto) ||
           (rewrite open_none by auto);
    eauto with erased wf fv;
    try solve [ apply equivalent_refl; t_closer ].
Qed.

Lemma open_reducible_nil2:
  forall tvars gamma,
    [ tvars; gamma ⊨ tnil : Nil ].
Proof.
  intros.
  apply open_reducible_singleton; steps; eauto with sets;
    eauto using open_reducible_nil, open_reducible_top.
Qed.

Lemma open_reducible_cons:
  forall tvars gamma h t H,
    [ tvars; gamma ⊨ h : H ] ->
    [ tvars; gamma ⊨ t : List ] ->
    [ tvars; gamma ⊨ tcons h t : List ].
Proof.
  intros.

  apply open_reducible_fold_gen2 with 0;
    repeat step || simp_spos;
    eauto with sets.

  apply open_reducible_right.
  apply open_reducible_pp;
    repeat step; eauto with sets;
    eauto using open_reducible_top.
Qed.

Lemma open_reducible_exists:
  forall tvars gamma A B t a,
    is_erased_type B ->
    wf B 1 ->
    subset (fv B) (support gamma) ->
    [ tvars; gamma ⊨ a: A ] ->
    [ tvars; gamma ⊨ t: open 0 B a ] ->
    [ tvars; gamma ⊨ t: T_exists A B ].
Proof.
  unfold open_reducible;
    repeat step || t_instantiate_sat3.

  unfold reducible, reduces_to; steps; t_closer.

  unfold reducible, reduces_to in H7; steps.

  exists v; repeat step || simp_red; t_closer.

  unfold reducible, reduces_to in H6; steps.

  exists v0; repeat step || t_substitutions; t_closer.

  eapply reducibility_values_ltr; eauto; steps; t_closer.
Qed.

Lemma open_reducible_cons2:
  forall tvars gamma h t H T,
    is_erased_type T ->
    wf T 0 ->
    subset (fv T) (support gamma) ->
    is_erased_term h ->
    wf h 0 ->
    subset (fv h) (support gamma) ->
    is_erased_term t ->
    wf t 0 ->
    subset (fv t) (support gamma) ->
    [ tvars; gamma ⊨ h : H ] ->
    [ tvars; gamma ⊨ t : T ] ->
    [ tvars; gamma ⊨ tcons h t : Cons H T ].
Proof.
  unfold Cons; repeat step.

  apply open_reducible_exists with h;
    repeat step || rewrite open_none in * by auto; t_closer.

  apply open_reducible_exists with t;
    repeat step ||
           (rewrite open_none in * by eauto with wf);
    t_closer.

  apply open_reducible_type_refine with uu;
    repeat step || rewrite pfv_shift2 ||
           simp_red ||
           (rewrite shift_nothing2 by auto) ||
           (rewrite open_none by auto);
    eauto with erased wf fv;
    try solve [ apply equivalent_refl; t_closer ];
    eauto 2 with sets;
    eauto using open_reducible_cons, open_reducible_top.
(*
  - apply open_reducible_top with (T_sum T_unit (T_prod H T)).
    apply open_reducible_right.
    apply open_reducible_pp; try eassumption; eauto with wf.
    rewrite open_none; auto.
*)
  - admit.
  - unfold open_reducible; repeat step || apply reducible_value_expr || simp_red.
    apply equivalent_refl; t_closer.
Admitted.

Definition list_match t1 t2 t3 :=
  sum_match t1 t2
    (shift_open 0 (shift_open 1 t3 (pi1 (lvar 0 term_var))) (pi2 (lvar 0 term_var))).

Lemma open_reducible_match:
  forall tvars gamma t t2 t3 T2 T3 x1 x2,
    ~ x1 ∈ support gamma ->
    ~ x2 ∈ support gamma ->
    [ tvars; gamma ⊨ t : List ] ->
    [ tvars; gamma ⊨ t2 : T2 ] ->
    [ tvars; (x1, T_top) :: (x2, List) :: gamma ⊨
        open 0 (open 1 t3 (fvar x1 term_var)) (fvar x2 term_var) :
        open 0 (open 1 T3 (fvar x1 term_var)) (fvar x2 term_var) ] ->
    [ tvars; gamma ⊨ list_match t t2 t3 : List_Match t T2 T3 ].
Proof.
  unfold list_match, List_Match;
    repeat step.
Admitted.
