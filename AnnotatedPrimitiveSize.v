From Stdlib Require Import List.

Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.ErasedPrimitiveSize.

Lemma annotated_reducible_size:
  forall Θ Γ t A,
    [[ Θ; Γ ⊨ t : A ]] ->
    [[ Θ; Γ ⊨ tsize t : T_nat ]].
Proof.
  steps; eauto using open_reducible_tsize.
Qed.
