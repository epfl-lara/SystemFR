Require Export SystemFR.ErasedTypeRefine.
Require Export SystemFR.ScalaDepSugar.

Opaque reducible_values.

Lemma reducible_singleton:
  forall ρ t T,
    valid_interpretation ρ ->
    [ ρ ⊨ t : T ] ->
    [ ρ ⊨ t : T_singleton T t ].
Proof.
  unfold T_singleton; steps.
  apply reducible_type_refine with uu;
    repeat step || apply reducible_value_expr || open_none ||
           (rewrite shift_nothing2 by eauto with wf) ||
           simp_red_goal;
    t_closer;
      try solve [ apply equivalent_refl; steps; t_closer ].
Qed.

Lemma reducible_singleton2:
  forall ρ t1 t2 T,
    valid_interpretation ρ ->
    [ t1 ≡ t2 ] ->
    [ ρ ⊨ t1 : T ] ->
    [ ρ ⊨ t1 : T_singleton T t2 ].
Proof.
  unfold T_singleton; steps.
  apply reducible_type_refine with uu;
    repeat step || apply reducible_value_expr || open_none ||
           (rewrite shift_nothing2 by eauto with wf) ||
           simp_red_goal;
    t_closer;
      try solve [ apply equivalent_refl; steps; t_closer ].
Qed.

Lemma reducible_values_singleton:
  forall ρ v t T,
    valid_interpretation ρ ->
    wf t 0 ->
    [ t ≡ v ] ->
    [ ρ ⊨ v : T ]v ->
    [ ρ ⊨ v : T_singleton T t ]v.
Proof.
  unfold T_singleton;
    repeat step || simp_red || exists uu ||
           (rewrite (open_none t) by auto) ||
           (rewrite shift_nothing2 by auto);
    t_closer;
    eauto using equivalent_sym.
Qed.

Lemma open_reducible_singleton:
  forall Θ Γ t T,
    is_erased_term t ->
    wf t 0 ->
    subset (fv t) (support Γ) ->
    [ Θ; Γ ⊨ t : T ] ->
    [ Θ; Γ ⊨ t : T_singleton T t ].
Proof.
  intros.
  unfold T_singleton.
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
