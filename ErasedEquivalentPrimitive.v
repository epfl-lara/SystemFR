Require Export SystemFR.ErasedPrimitive.


Lemma reducible_values_primitive_EqEquiv1:
  forall ρ v1 v2,
    [ ρ ⊨ v1 : T_nat ]v ->
    [ ρ ⊨ v2 : T_nat ]v ->
    [ binary_primitive Eq v1 v2 ≡ ttrue ] ->
    [ v1 ≡ v2 ].
Proof.
  unfold reduces_to; intros; repeat simp_red; repeat is_nat_value_buildable; steps.
  apply_anywhere equivalent_true; last_step_binary_primitive.
  rewrite PeanoNat.Nat.eqb_eq in *; subst.
  unfold equivalent_terms; steps; eauto with erased values wf fv.
Qed.

Opaque Coq.Init.Wf.Fix_F.
Opaque  Subterm.FixWf.

Lemma reducible_primitive_EqEquiv1:
  forall ρ t1 t2,
    valid_interpretation ρ ->
    [ ρ ⊨ t1 : T_nat ] ->
    [ ρ ⊨ t2 : T_nat ] ->
    [ binary_primitive Eq t1 t2 ≡ ttrue ] ->
    [ t1 ≡ t2 ].
Proof.
  intros;
    repeat steps || simp_red || is_nat_value_buildable || unfold closed_term in * || top_level_unfold reduces_to ; eauto with erased wf.
  eapply equivalent_trans; [
    apply equivalent_star; eauto with erased wf fv | idtac].
  eapply equivalent_sym, equivalent_trans; [equivalent_star | idtac].
  apply equivalent_sym.
  eapply (reducible_values_primitive_EqEquiv1 ρ); unfold reduces_to; steps;
    autorewrite with reducible_values; eauto with cbvlemmas values reducible_values.
  eapply equivalent_trans; [idtac | eauto using equivalent_refl with fv erased values].
  apply equivalent_sym, equivalent_star;
    repeat steps || list_utils ; eauto with wf erased fv.
  apply star_smallstep_binary_primitive; eauto with values.
Qed.

Lemma open_reducible_primitive_EqEquiv1:
  forall Θ Γ t1 t2,
    [Θ; Γ ⊨ t1 : T_nat] ->
    [Θ; Γ ⊨ t2 : T_nat] ->
    [Θ; Γ ⊨ binary_primitive Eq t1 t2 ≡ ttrue ] ->
    [Θ; Γ ⊨ t1 ≡ t2].
Proof. unfold open_reducible, open_equivalent; steps;
         eauto using reducible_primitive_EqEquiv1.
Qed.

Hint Resolve open_reducible_primitive_EqEquiv1: primitives.

Lemma equivalent_build_nat:
  forall n1 n2,
    [build_nat n1 ≡ build_nat n2] ->
    n1 = n2.
Proof.
  unfold equivalent_terms; steps.
  specialize (H6 (binary_primitive Eq (lvar 0 term_var) (build_nat n2))); steps.
  repeat (rewrite open_none in H6; eauto with wf).
  assert (binary_primitive Eq (build_nat n1) (build_nat n2) ~> ttrue). {
    apply last_step_binary_primitive; eauto with values.
    apply H6; try Psatz.lia; eauto with wf smallstep.
    apply star_one. pose proof (SPBetaEq _ _ n2 n2 eq_refl eq_refl); steps.
    rewrite PeanoNat.Nat.eqb_neq in *; steps.
    }
  t_invert_step; repeat steps || rewrite PeanoNat.Nat.eqb_eq in * || build_nat_inj.
Qed.

Ltac equivalent_build_nat :=
  match goal with
  | H: [ build_nat ?n1 ≡ build_nat ?n2 ] |- _ => apply equivalent_build_nat in H; subst
  end.


Lemma reducible_values_primitive_EqEquiv2:
  forall ρ v1 v2,
    [ ρ ⊨ v1 : T_nat ]v ->
    [ ρ ⊨ v2 : T_nat ]v ->
    [ v1 ≡ v2 ] ->
    [ binary_primitive Eq v1 v2 ≡ ttrue ].
Proof.
  unfold reduces_to; repeat simp_red || is_nat_value_buildable || steps || equivalent_build_nat.
  eapply equivalent_star; repeat steps || list_utils; eauto with smallstep wf fv erased.
  apply star_one. epose proof (SPBetaEq _ _ n0 n0); repeat rewrite PeanoNat.Nat.eqb_neq in * || steps.
Qed.

Lemma reducible_primitive_EqEquiv2:
  forall ρ t1 t2,
    (valid_interpretation ρ) ->
    [ ρ ⊨ t1 : T_nat ] ->
    [ ρ ⊨ t2 : T_nat ] ->
    [ t1 ≡ t2 ] ->
    [ binary_primitive Eq t1 t2 ≡ ttrue ].
Proof.
  intros;
    repeat steps || simp_red || is_nat_value_buildable || unfold closed_term in * || top_level_unfold reduces_to ; eauto with erased wf.

  eapply equivalent_trans.
  apply equivalent_star; repeat steps || list_utils ; eauto with erased wf fv.
  apply star_smallstep_binary_primitive; eauto using cbv_value_build_nat.
  unshelve eapply reducible_values_primitive_EqEquiv2; unfold reduces_to; steps;
    autorewrite with reducible_values; eauto with cbvlemmas values reducible_values.
  eapply equivalent_trans. apply equivalent_sym. equivalent_star.
  eapply equivalent_trans; eauto. equivalent_star.
Qed.


Lemma open_reducible_primitive_EqEquiv2:
  forall Θ Γ t1 t2,
    [Θ; Γ ⊨ t1 : T_nat] ->
    [Θ; Γ ⊨ t2 : T_nat] ->
    [Θ; Γ ⊨ t1 ≡ t2] ->
    [Θ; Γ ⊨ binary_primitive Eq t1 t2 ≡ ttrue ].
Proof. unfold open_reducible, open_equivalent; steps;
         eauto using reducible_primitive_EqEquiv2.
Qed.
Hint Resolve open_reducible_primitive_EqEquiv2: primitives.

Lemma open_reducible_primitive_EqSym:
  forall Θ Γ t1 t2,
    [Θ; Γ ⊨ t1 : T_nat] ->
    [Θ; Γ ⊨ t2 : T_nat] ->
    [Θ; Γ ⊨ binary_primitive Eq t1 t2 ≡ ttrue ] ->
    [Θ; Γ ⊨ binary_primitive Eq t2 t1 ≡ ttrue ].
Proof.
  steps.
  apply open_reducible_primitive_EqEquiv2; eauto.
  assert ([Θ; Γ ⊨ t1 ≡ t2]). apply open_reducible_primitive_EqEquiv1; eauto.
  unfold open_equivalent in * ; steps ; eauto using equivalent_sym.
Qed.
Hint Resolve open_reducible_primitive_EqSym: primitives.
