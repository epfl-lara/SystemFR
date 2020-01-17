Require Export SystemFR.Judgments.

Lemma annotated_reducible_typeability:
  forall tvars gamma t T,
    [[ tvars; gamma ⊨ t : T ]] ->
    [[ tvars; gamma ⊨ typecheck t T : T ]].
Proof.
  unfold annotated_reducible; steps.
Qed.
