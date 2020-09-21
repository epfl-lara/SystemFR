Require Export SystemFR.Judgments.
Require Export SystemFR.ReducibilityLemmas.

Opaque reducible_values.

Lemma annotated_reducible_sub:
  forall Θ Γ t T1 T2,
    [[ Θ; Γ ⊨ T1 <: T2 ]] ->
    [[ Θ; Γ ⊨ t : T1 ]] ->
    [[ Θ; Γ ⊨ t : T2 ]].
Proof.
  unfold open_reducible, open_subtype;
    repeat step; eauto using reducible_values_exprs.
Qed.
