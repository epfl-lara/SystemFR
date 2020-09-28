Require Export SystemFR.ErasedEquivalentPrimitive.
Require Export SystemFR.Judgments.



Lemma annotated_reducible_primitive_EqEquiv1:
  forall Θ Γ t1 t2,
    [[Θ; Γ ⊨ t1 : T_nat]] ->
    [[Θ; Γ ⊨ t2 : T_nat]] ->
    [[Θ; Γ ⊨ binary_primitive Eq t1 t2 ≡ ttrue ]] ->
    [[Θ; Γ ⊨ t1 ≡ t2]].
Proof. steps; eauto with primitives. Qed.

Lemma annotated_reducible_primitive_EqEquiv2:
  forall Θ Γ t1 t2,
    [[Θ; Γ ⊨ t1 : T_nat]] ->
    [[Θ; Γ ⊨ t2 : T_nat]] ->
    [[Θ; Γ ⊨ t1 ≡ t2]] ->
    [[Θ; Γ ⊨ binary_primitive Eq t1 t2 ≡ ttrue ]] .
Proof. steps; eauto with primitives. Qed.


Lemma annotated_reducible_primitive_Eq_sym:
  forall Θ Γ t1 t2,
    [[Θ; Γ ⊨ t1 : T_nat]] ->
    [[Θ; Γ ⊨ t2 : T_nat]] ->
    [[Θ; Γ ⊨ binary_primitive Eq t1 t2 ≡ ttrue ]] ->
    [[Θ; Γ ⊨ binary_primitive Eq t2 t1 ≡ ttrue ]].
Proof. steps; eauto with primitives. Qed.
