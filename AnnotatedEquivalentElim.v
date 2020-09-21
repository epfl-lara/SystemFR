Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.Judgments.
Require Export SystemFR.ErasedEquivalentElim.

Lemma annotated_equivalent_elim:
  forall Θ Γ t1 t2 T,
    wf T 0 ->
    subset (fv T) (support Γ) ->
    [[ Θ; Γ ⊨ t1 ≡ t2 ]] ->
    [[ Θ; Γ ⊨ t1: T ]] ->
    [[ Θ; Γ ⊨ t2: T ]].
Proof.
  intros; eapply open_reducible_equivalent_elim;
    steps;
    side_conditions.
Qed.
