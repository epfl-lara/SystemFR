Require Export SystemFR.ErasedPrimitive.
Require Export SystemFR.Judgments.

Lemma annotated_reducible_primitive_Not:
  forall Θ Γ t1,
    [[ Θ; Γ ⊨ t1 : T_bool ]] ->
    [[ Θ; Γ ⊨ unary_primitive Not t1 : T_bool]].
Proof. steps; eauto with primitives. Qed.

Lemma annotated_reducible_primitive_Plus:
  forall Θ Γ t1 t2,
    [[ Θ; Γ ⊨ t1 : T_nat ]] ->
    [[ Θ; Γ ⊨ t2 : T_nat ]] ->
    [[ Θ; Γ ⊨ binary_primitive Plus t1 t2 : T_nat]].
Proof. steps; eauto with primitives. Qed.

Lemma annotated_reducible_primitive_Minus:
  forall Θ Γ t1 t2,
    [[ Θ; Γ ⊨ t1 : T_nat ]] ->
    [[ Θ; Γ ⊨ t2 : T_nat ]] ->
    [[ Θ; Γ ⊨ binary_primitive Geq t1 t2 ≡ ttrue ]] ->
    [[ Θ; Γ ⊨ binary_primitive Minus t1 t2 : T_nat]].
Proof. steps; eauto with primitives. Qed.

Lemma annotated_reducible_primitive_Mul:
  forall Θ Γ t1 t2,
    [[ Θ; Γ ⊨ t1 : T_nat ]] ->
    [[ Θ; Γ ⊨ t2 : T_nat ]] ->
    [[ Θ; Γ ⊨ binary_primitive Mul t1 t2 : T_nat]].
Proof. steps; eauto with primitives. Qed.

Lemma annotated_reducible_primitive_Div:
  forall Θ Γ t1 t2,
    [[ Θ; Γ ⊨ t1 : T_nat ]] ->
    [[ Θ; Γ ⊨ t2 : T_nat ]] ->
    [[ Θ; Γ ⊨ binary_primitive Gt t2 zero ≡ ttrue ]] ->
    [[ Θ; Γ ⊨ binary_primitive Div t1 t2 : T_nat]].
Proof. steps; eauto with primitives. Qed.

Lemma annotated_reducible_primitive_Lt:
  forall Θ Γ t1 t2,
    [[ Θ; Γ ⊨ t1 : T_nat ]] ->
    [[ Θ; Γ ⊨ t2 : T_nat ]] ->
    [[ Θ; Γ ⊨ binary_primitive Lt t1 t2 : T_bool]].
Proof. steps; eauto with primitives. Qed.

Lemma annotated_reducible_primitive_Leq:
  forall Θ Γ t1 t2,
    [[ Θ; Γ ⊨ t1 : T_nat ]] ->
    [[ Θ; Γ ⊨ t2 : T_nat ]] ->
    [[ Θ; Γ ⊨ binary_primitive Leq t1 t2 : T_bool]].
Proof. steps; eauto with primitives. Qed.

Lemma annotated_reducible_primitive_Gt:
  forall Θ Γ t1 t2,
    [[ Θ; Γ ⊨ t1 : T_nat ]] ->
    [[ Θ; Γ ⊨ t2 : T_nat ]] ->
    [[ Θ; Γ ⊨ binary_primitive Gt t1 t2 : T_bool]].
Proof. steps; eauto with primitives. Qed.

Lemma annotated_reducible_primitive_Geq:
  forall Θ Γ t1 t2,
    [[ Θ; Γ ⊨ t1 : T_nat ]] ->
    [[ Θ; Γ ⊨ t2 : T_nat ]] ->
    [[ Θ; Γ ⊨ binary_primitive Geq t1 t2 : T_bool]].
Proof. steps; eauto with primitives. Qed.

Lemma annotated_reducible_primitive_Eq:
  forall Θ Γ t1 t2,
    [[ Θ; Γ ⊨ t1 : T_nat ]] ->
    [[ Θ; Γ ⊨ t2 : T_nat ]] ->
    [[ Θ; Γ ⊨ binary_primitive Eq t1 t2 : T_bool]].
Proof. steps; eauto with primitives. Qed.

Lemma annotated_reducible_primitive_Neq:
  forall Θ Γ t1 t2,
    [[ Θ; Γ ⊨ t1 : T_nat ]] ->
    [[ Θ; Γ ⊨ t2 : T_nat ]] ->
    [[ Θ; Γ ⊨ binary_primitive Neq t1 t2 : T_bool]].
Proof. steps; eauto with primitives. Qed.

Lemma annotated_reducible_primitive_And:
  forall Θ Γ t1 t2,
    [[ Θ; Γ ⊨ t1 : T_bool ]] ->
    [[ Θ; Γ ⊨ t2 : T_bool ]] ->
    [[ Θ; Γ ⊨ binary_primitive And t1 t2 : T_bool]].
Proof. steps; eauto with primitives. Qed.

Lemma annotated_reducible_primitive_Or:
  forall Θ Γ t1 t2,
    [[ Θ; Γ ⊨ t1 : T_bool ]] ->
    [[ Θ; Γ ⊨ t2 : T_bool ]] ->
    [[ Θ; Γ ⊨ binary_primitive Or t1 t2 : T_bool]].
Proof. steps; eauto with primitives. Qed.
