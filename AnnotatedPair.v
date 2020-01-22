Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.ErasedPair.

Lemma annotated_reducible_pp:
  forall tvars gamma A B t1 t2,
    wf B 1 ->
    is_annotated_type B ->
    is_annotated_term t1 ->
    subset (fv B) (support gamma) ->
    [[ tvars; gamma ⊨ t1 : A ]] ->
    [[ tvars; gamma ⊨ t2 : open 0 B t1 ]] ->
    [[ tvars; gamma ⊨ pp t1 t2 : T_prod A B ]].
Proof.
  unfold annotated_reducible; steps.
  apply open_reducible_pp; repeat step || erase_open; side_conditions.
Qed.

Lemma annotated_reducible_pi1:
  forall tvars gamma t A B,
    [[ tvars; gamma ⊨ t : T_prod A B ]] ->
    [[ tvars; gamma ⊨ pi1 t : A ]].
Proof.
  unfold annotated_reducible; steps; eauto using open_reducible_pi1.
Qed.

Lemma annotated_reducible_pi2:
  forall tvars gamma t A B,
    wf B 1 ->
    is_annotated_type B ->
    is_annotated_term t ->
    subset (fv B) (support gamma) ->
    [[ tvars; gamma ⊨ t : T_prod A B ]] ->
    [[ tvars; gamma ⊨ pi2 t : open 0 B (pi1 t) ]].
Proof.
  unfold annotated_reducible; repeat step || erase_open.
  eapply open_reducible_pi2;
    steps;
    side_conditions.
Qed.
