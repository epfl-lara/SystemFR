Require Export SystemFR.ScalaDepSugar.
Require Export SystemFR.ErasedRecGen.
Require Export SystemFR.ErasedSum.
Require Export SystemFR.ErasedPair.
Require Export SystemFR.ErasedTop.
Require Export SystemFR.ErasedSingleton.
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

Lemma no_type_fvar_List:
  forall vars, no_type_fvar List vars.
Proof.
  unfold no_type_fvar; steps.
Qed.

Lemma cbv_value_nil: cbv_value tnil.
Proof.
  unfold tnil; eauto with values.
Qed.

Lemma open_tnil_helper:
  forall Θ Γ,
    [ Θ; Γ ⊨ tnil : T_singleton List tnil ].
Proof.
  intros.
  apply open_reducible_singleton; steps; eauto with sets;
    eauto using open_reducible_nil, open_reducible_top.
Qed.

Lemma open_tnil:
  forall Γ, [ Γ ⊨ tnil : T_singleton List tnil ].
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
    [ Γ ⊨ tcons h t : T_singleton (Cons H T) (tcons h t) ].
Proof.
  intros; apply open_reducible_singleton; repeat step || sets;
    eauto using open_tcons_helper.
Qed.

Opaque tnil.
Opaque List.

Lemma reducible_nil:
  forall ρ,
    valid_interpretation ρ ->
    [ ρ | tnil : List ]v.
Proof.
  unshelve epose proof (open_reducible_nil nil nil); steps.
  rewrite (List.app_nil_end ρ).
  apply reducible_unused_many2; repeat step || apply reducible_expr_value;
    eauto using no_type_fvar_List;
    eauto using cbv_value_nil.
  unfold open_reducible in *; repeat step.
  unshelve epose proof (H nil nil _ _ _); steps.
Qed.
