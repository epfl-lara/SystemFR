Require Export SystemFR.ReducibilityLemmas.

Inductive untangle: tree -> tree -> Prop :=
| UntangleRefl: forall T, untangle T T
.

Lemma untangle_open_equivalent_types:
  forall Θ Γ T1 T2,
    untangle T1 T2 ->
    [ Θ; Γ ⊨ T1 = T2 ].
Proof.
Admitted.
