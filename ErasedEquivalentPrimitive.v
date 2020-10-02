Require Export SystemFR.ErasedPrimitive.
Require Import Coq.Strings.String.


Lemma reducible_values_primitive_EqEquiv1:
  forall v1 v2,
    cbv_value v1 ->
    cbv_value v2 ->
    [ binary_primitive Eq v1 v2 ≡ ttrue ] ->
    [ v1 ≡ v2 ].
Proof.
  unfold reduces_to; intros; repeat simp_red; repeat is_nat_value_buildable; steps.
  apply_anywhere equivalent_true. last_step_binary_primitive.
   rewrite PeanoNat.Nat.eqb_eq in *; subst.
  unfold equivalent_terms; steps; eauto with erased values wf fv.
Qed.

Opaque Coq.Init.Wf.Fix_F.
Opaque  Subterm.FixWf.

Lemma reducible_primitive_EqEquiv1:
  forall t1 t2,
    [ binary_primitive Eq t1 t2 ≡ ttrue ] ->
    [ t1 ≡ t2 ].
Proof.
  steps.
  pose proof H.
  apply_anywhere equivalent_true.
  t_invert_star; eauto with values. steps.
  eapply equivalent_trans; [ top_level_unfold equivalent_terms;
    apply equivalent_star; eauto with erased wf fv; t_closer | idtac].
  eapply equivalent_sym, equivalent_trans; [equivalent_star | idtac].
  apply equivalent_sym.
  eapply reducible_values_primitive_EqEquiv1; unfold reduces_to; steps;
    autorewrite with reducible_values; eauto with cbvlemmas values reducible_values.
  eapply equivalent_trans; [idtac | eauto using equivalent_refl with fv erased values].
  apply equivalent_sym, equivalent_star;
    repeat steps || list_utils || top_level_unfold equivalent_terms ; eauto with wf erased fv.
  apply star_smallstep_binary_primitive; eauto with values.
Qed.

Lemma open_reducible_primitive_EqEquiv1:
  forall Θ Γ t1 t2,
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

Lemma open_reducible_primitive_Eq_args:
  forall Θ Γ t1 t2,
    [Θ; Γ ⊨ binary_primitive Eq t1 t2 ≡ ttrue ] ->
    [Θ; Γ ⊨ t1 : T_nat] /\ [Θ; Γ ⊨ t2 : T_nat].
Proof.
  intros. unfold open_equivalent, open_reducible in *; steps; specialize (H ρ lterms); intuition auto;
  assert (closed_term (psubstitute t2 lterms term_var)) by
      (unfold equivalent_terms, closed_term, open_equivalent, open_reducible in *; repeat steps || list_utils);
  assert (closed_term (psubstitute t1 lterms term_var)) by
      (unfold equivalent_terms, closed_term, open_equivalent, open_reducible in *; repeat steps || list_utils);
  apply_anywhere equivalent_true;
  eapply_anywhere star_smallstep_binary_primitive_inv; eauto with values; steps;
  step_inversion scbv_step; steps;
  unfold reduces_to; steps; eauto with values smallstep;
  eexists; split; eauto;
  rewrite reducible_values_equation_4; apply is_nat_value_build_nat.
Qed.


Lemma open_reducible_primitive_EqSym:
  forall Θ Γ t1 t2,
    [Θ; Γ ⊨ binary_primitive Eq t1 t2 ≡ ttrue ] ->
    [Θ; Γ ⊨ binary_primitive Eq t2 t1 ≡ ttrue ].
Proof.
  steps.
  apply open_reducible_primitive_EqEquiv2;
    try solve [
          apply_anywhere open_reducible_primitive_Eq_args; steps].
  assert ([Θ; Γ ⊨ t1 ≡ t2]). apply open_reducible_primitive_EqEquiv1; eauto.
  unfold open_equivalent in * ; steps ; eauto using equivalent_sym.
Qed.
Hint Resolve open_reducible_primitive_EqSym: primitives.

Lemma reducible_values_primitive_Lt_sound:
  forall a b, cbv_value a ->
         cbv_value b ->
         [ binary_primitive Lt a b ≡ ttrue] ->
         tree_size a < tree_size b.
Proof.
  intros.
  apply_anywhere equivalent_true. last_step_binary_primitive.
  repeat rewrite tree_size_build_nat; steps. Psatz.lia.
Qed.

Ltac reducible_values_primitive_Lt_sound :=
  match goal with
  | H: binary_primitive Lt ?a ?b ~>* ttrue |- _ =>
    cbv_value a; cbv_value b;
    poseNew (Mark (a,b) "reducible_values_primitive_Lt_sound");
    unshelve epose proof (reducible_values_primitive_Lt_sound a b _ _ H)
  | H: [ binary_primitive Lt ?a ?b ≡ ttrue ] |- _ =>
    cbv_value a; cbv_value b;
    poseNew (Mark (a,b) "reducible_values_primitive_Lt_sound");
    unshelve epose proof (reducible_values_primitive_Lt_sound a b _ _ _)
  end.
