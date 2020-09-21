Require Export SystemFR.Judgments.
Require Export SystemFR.ErasedErr.

Lemma annotated_reducible_err:
  forall Θ Γ T,
    [[ Θ; Γ ⊨ tfalse ≡ ttrue ]] ->
    [[ Θ; Γ ⊨ err T : T ]].
Proof.
  intros; eauto using open_reducible_err.
Qed.
