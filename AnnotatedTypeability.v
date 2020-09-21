Require Export SystemFR.Judgments.

Lemma annotated_reducible_typeability:
  forall Θ Γ t T,
    [[ Θ; Γ ⊨ t : T ]] ->
    [[ Θ; Γ ⊨ typecheck t T : T ]].
Proof.
  steps.
Qed.
