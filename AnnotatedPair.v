Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.ErasedPair.

Lemma annotated_reducible_pp:
  forall Θ Γ A B t1 t2,
    wf B 1 ->
    is_annotated_type B ->
    is_annotated_term t1 ->
    subset (fv B) (support Γ) ->
    [[ Θ; Γ ⊨ t1 : A ]] ->
    [[ Θ; Γ ⊨ t2 : open 0 B t1 ]] ->
    [[ Θ; Γ ⊨ pp t1 t2 : T_prod A B ]].
Proof.
  intros; apply open_reducible_pp; repeat step || erase_open; side_conditions.
Qed.

Lemma annotated_reducible_pi1:
  forall Θ Γ t A B,
    [[ Θ; Γ ⊨ t : T_prod A B ]] ->
    [[ Θ; Γ ⊨ pi1 t : A ]].
Proof.
  steps; eauto using open_reducible_pi1.
Qed.

Lemma annotated_reducible_pi2:
  forall Θ Γ t A B,
    wf B 1 ->
    is_annotated_type B ->
    is_annotated_term t ->
    subset (fv B) (support Γ) ->
    [[ Θ; Γ ⊨ t : T_prod A B ]] ->
    [[ Θ; Γ ⊨ pi2 t : open 0 B (pi1 t) ]].
Proof.
  repeat step || erase_open.
  eapply open_reducible_pi2;
    steps;
    side_conditions.
Qed.
