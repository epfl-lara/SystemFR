Require Export SystemFR.ErasedTypeRefine.
Require Export SystemFR.ScalaDepSugar.

Opaque reducible_values.

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
