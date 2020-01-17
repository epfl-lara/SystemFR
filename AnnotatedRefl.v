Require Export SystemFR.Judgments.
Require Export SystemFR.ErasedRefl.

Lemma annotated_reducible_refl:
  forall tvars gamma t1 t2,
    [[ tvars; gamma ⊨ t1 ≡ t2 ]] ->
    [[ tvars; gamma ⊨ trefl t1 t2 : T_equiv t1 t2 ]].
Proof.
  unfold equivalent, annotated_reducible;
    repeat step;
    eauto using open_reducible_refl.
Qed.
