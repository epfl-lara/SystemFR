Require Export SystemFR.Judgments.
Require Export SystemFR.ErasedErr.

Lemma annotated_reducible_err:
  forall tvars gamma T,
    [[ tvars; gamma ⊨ tfalse ≡ ttrue ]] ->
    [[ tvars; gamma ⊨ err T : T ]].
Proof.
  unfold annotated_reducible, annotated_equivalent;
    repeat step; eauto using open_reducible_err.
Qed.
