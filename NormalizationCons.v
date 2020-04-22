Require Export SystemFR.ReducibilityDefinition.
Require Export SystemFR.TypeSugar2.

Lemma open_ncons: forall Θ Γ T1 T2 T1' T2',
  [ Θ; Γ ⊨ T1 = T1' ] ->
  [ Θ; Γ ⊨ T2 = T2' ] ->
  [ Θ; Γ ⊨ Cons T1 T2 = Cons T1' T2' ].
Proof.
Admitted.
