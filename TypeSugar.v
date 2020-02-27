Require Export SystemFR.Trees.
Require Export SystemFR.SomeTerms.
Require Export SystemFR.ShiftOpen.
Require Export SystemFR.ErasedArrow.
Require Export SystemFR.ErasedTop.
Require Export SystemFR.ReducibilityEquivalent.

Opaque reducible_values.

Definition T_not T := T_arrow T T_bot.
Definition T_reducible t T := T_exists T (T_equiv (lvar 0 term_var) t).
Definition T_complement T := T_type_refine T_top (T_not (T_reducible (lvar 0 term_var) T)).
Definition T_ITE T A B := T_union (T_type_refine A T) (T_type_refine B (T_not T)).
Definition T_ite t A B := T_union (T_refine A t) (T_refine B (negate t)).
Definition T_sum_match t A B := T_union (open 0 A (unfold_left t)) (open 0 B (unfold_right t)).
Definition T_nat_match t T0 Ts := T_union (T_type_refine T0 (T_equiv t zero)) (open 0 Ts (notype_tpred t)).
Definition T_image f T := T_type_refine T_top (T_exists T (T_equiv (lvar 1 term_var) (app f (lvar 0 term_var)))).

Lemma is_erased_type_T_reducible:
  forall t T,
    is_erased_term t ->
    is_erased_type T ->
    is_erased_type (T_reducible t T).
Proof.
  unfold T_reducible;
    repeat step;
    eauto with erased.
Qed.

Lemma open_T_reducible:
  forall t T k rep,
    wf t 0 ->
    wf T 0 ->
    open k (T_reducible t T) rep = T_reducible t T.
Proof.
  unfold T_reducible;
    repeat step || t_equality || rewrite open_none in * by eauto with wf.
Qed.

Lemma reducible_values_type_prop:
  forall theta t T p,
    wf t 0 ->
    is_erased_type T ->
    wf T 0 ->
    pfv T term_var = nil ->
    valid_interpretation theta ->
    reducible_values theta p (T_reducible t T) ->
    reducible theta t T.
Proof.
  unfold T_reducible;
    repeat step || simp_red || (rewrite open_none in * by t_closer).
  eapply reducibility_equivalent2; eauto;
    repeat step;
    eauto using reducible_value_expr.
Qed.

Lemma reducible_type_prop:
  forall theta t T p,
    wf t 0 ->
    is_erased_type T ->
    wf T 0 ->
    pfv T term_var = nil ->
    valid_interpretation theta ->
    reducible theta p (T_reducible t T) ->
    reducible theta t T.
Proof.
  intros.
  top_level_unfold reducible; top_level_unfold reduces_to;
    repeat step;
    eauto using reducible_values_type_prop.
Qed.

Lemma reducible_values_prop_type:
  forall theta t T,
    reducible theta t T ->
    reducible_values theta uu (T_reducible t T).
Proof.
  unfold T_reducible, reducible, reduces_to;
    repeat step || simp_red;
    t_closer.

  exists v;
    repeat step || simp_red || rewrite open_none in * by t_closer;
    t_closer.

  apply equivalent_sym; equivalent_star.
Qed.
