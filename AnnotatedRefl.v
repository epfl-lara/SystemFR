Require Export SystemFR.Judgments.
Require Export SystemFR.ErasedRefl.

Lemma annotated_reducible_refl:
  forall Θ Γ t1 t2,
    [[ Θ; Γ ⊨ t1 ≡ t2 ]] ->
    [[ Θ; Γ ⊨ trefl t1 t2 : T_equiv t1 t2 ]].
Proof.
  unfold open_equivalent;
    repeat step;
    eauto using open_reducible_refl.
Qed.
