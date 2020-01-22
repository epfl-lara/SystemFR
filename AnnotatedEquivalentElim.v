Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.Judgments.
Require Export SystemFR.ErasedEquivalentElim.

Lemma annotated_equivalent_elim:
  forall tvars gamma t1 t2 T,
    wf T 0 ->
    subset (fv T) (support gamma) ->
    [[ tvars; gamma ⊨ t1 ≡ t2 ]] ->
    [[ tvars; gamma ⊨ t1: T ]] ->
    [[ tvars; gamma ⊨ t2: T ]].
Proof.
  unfold annotated_equivalent, annotated_reducible;
    repeat step.

  eapply open_reducible_equivalent_elim;
    steps;
    side_conditions.
Qed.
