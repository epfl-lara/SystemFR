Require Export SystemFR.ReducibilityDefinition.
Require Export SystemFR.ScalaDepSugar.

Lemma nbase1: forall ρ, [ ρ ⊨ T_top = T_top ].
Proof.
  unfold equivalent_types. steps.
Qed.

Lemma nbase2: forall ρ, [ ρ ⊨ List = List ].
Proof.
  unfold equivalent_types; steps.
Qed.

Lemma open_nbase1: forall Θ Γ, [ Θ; Γ ⊨ T_top = T_top ].
Proof.
  unfold open_equivalent_types; eauto using nbase1.
Qed.

Lemma open_nbase2: forall Θ Γ, [ Θ; Γ ⊨ List = List ].
Proof.
  unfold open_equivalent_types; eauto using nbase2.
Qed.
