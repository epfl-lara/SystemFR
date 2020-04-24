Require Export SystemFR.TypeSugar2.
Require Export SystemFR.ErasedRecGen.
Require Export SystemFR.ErasedSum.
Require Export SystemFR.ErasedPair.
Require Export SystemFR.ErasedTop.
Require Export SystemFR.ErasedTypeRefine.
Require Export SystemFR.ErasedQuant.
Require Export SystemFR.ReducibilitySubtype.

Opaque strictly_positive.
Opaque reducible_values.

Lemma open_reducible_nil:
  forall Θ Γ,
    [ Θ; Γ ⊨ tnil : List ].
Proof.
  intros.

  apply open_reducible_fold_gen2 with 0;
    repeat step || simp_spos;
    eauto with sets.

  apply open_reducible_left.
  apply open_reducible_unit.
Qed.

Lemma open_reducible_singleton:
  forall Θ Γ t T,
    is_erased_term t ->
    wf t 0 ->
    subset (fv t) (support Γ) ->
    [ Θ; Γ ⊨ t : T ] ->
    [ Θ; Γ ⊨ t : tsingleton T t ].
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

Lemma open_tnil_helper:
  forall Θ Γ,
    [ Θ; Γ ⊨ tnil : tsingleton List tnil ].
Proof.
  intros.
  apply open_reducible_singleton; steps; eauto with sets;
    eauto using open_reducible_nil, open_reducible_top.
Qed.

Lemma open_tnil:
  forall Γ, [ Γ ⊨ tnil : tsingleton List tnil ].
Proof.
  eauto using open_tnil_helper.
Qed.

Lemma open_reducible_cons:
  forall Θ Γ h t H,
    [ Θ; Γ ⊨ h : H ] ->
    [ Θ; Γ ⊨ t : List ] ->
    [ Θ; Γ ⊨ tcons h t : List ].
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

Opaque List.

Lemma open_tcons_helper:
  forall Θ Γ h t H T,
    is_erased_type T ->
    wf T 0 ->
    subset (fv T) (support Γ) ->
    is_erased_term h ->
    wf h 0 ->
    subset (fv h) (support Γ) ->
    is_erased_term t ->
    wf t 0 ->
    subset (fv t) (support Γ) ->
    [ Θ; Γ ⊨ h : H ] ->
    [ Θ; Γ ⊨ t : T ] ->
    [ Θ; Γ ⊨ T <: List ] ->
    [ Θ; Γ ⊨ tcons h t : Cons H T ].
Proof.
  unfold Cons; repeat step.

  apply open_reducible_exists with h;
    repeat step || rewrite open_none in * by auto; t_closer;
      eauto using is_erased_list, wf_list.

  apply open_reducible_exists with t;
    repeat step || (rewrite open_list in *) ||
           (rewrite open_none in * by eauto with wf);
    t_closer;
    eauto using is_erased_list, wf_list.

  apply open_reducible_type_refine with uu;
    repeat step || rewrite pfv_shift2 ||
           simp_red ||
           (rewrite shift_nothing2 by auto) ||
           (rewrite open_none by auto);
    eauto with erased wf fv;
    try solve [ apply equivalent_refl; t_closer ];
    eauto 2 with sets.

  - eauto using open_reducible_cons, open_subtype_reducible.
  - unfold open_reducible; repeat step || apply reducible_value_expr || simp_red.
    apply equivalent_refl; t_closer.
Qed.

Lemma open_tcons:
  forall Γ h t H T,
    is_erased_type T ->
    wf T 0 ->
    subset (fv T) (support Γ) ->
    is_erased_term h ->
    wf h 0 ->
    subset (fv h) (support Γ) ->
    is_erased_term t ->
    wf t 0 ->
    subset (fv t) (support Γ) ->
    [ Γ ⊨ h : H ] ->
    [ Γ ⊨ t : T ] ->
    [ Γ ⊨ T <: List ] ->
    [ Γ ⊨ tcons h t : Cons H T ].
Proof.
  eauto using open_tcons_helper.
Qed.

Definition list_match t1 t2 t3 :=
  sum_match t1 t2
    (shift_open 0 (shift_open 1 t3 (pi1 (lvar 0 term_var))) (pi2 (lvar 0 term_var))).

Lemma open_tmatch:
  forall Θ Γ t t2 t3 T2 T3 x1 x2,
    ~ x1 ∈ support Γ ->
    ~ x2 ∈ support Γ ->
    [ Θ; Γ ⊨ t : List ] ->
    [ Θ; Γ ⊨ t2 : T2 ] ->
    [ Θ; (x1, T_top) :: (x2, List) :: Γ ⊨
        open 0 (open 1 t3 (fvar x1 term_var)) (fvar x2 term_var) :
        open 0 (open 1 T3 (fvar x1 term_var)) (fvar x2 term_var) ] ->
    [ Θ; Γ ⊨ list_match t t2 t3 : List_Match t T2 T3 ].
Proof.
  unfold list_match, List_Match;
    repeat step.
Admitted.
