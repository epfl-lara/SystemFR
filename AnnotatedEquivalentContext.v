Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.RedTactics.
Require Export SystemFR.EquivalentContext.

Lemma annotated_equivalence_context:
  forall Θ Γ C t1 t2,
    wf C 1 ->
    is_annotated_term C ->
    subset (fv C) (support Γ) ->
    is_annotated_term t1 ->
    is_annotated_term t2 ->
    [[ Θ; Γ ⊨ t1 ≡ t2 ]] ->
    [[ Θ; Γ ⊨ open 0 C t1 ≡ open 0 C t2 ]].
Proof.
  unfold open_equivalent;
    repeat step || erase_open || t_substitutions || apply equivalent_context;
    eauto with erased;
    eauto with wf;
    eauto with fv.
Qed.

Lemma annotated_equivalence_lambdas:
  forall Θ Γ t1 t2 A B,
    is_annotated_term t1 ->
    is_annotated_term t2 ->
    is_annotated_type A ->
    wf A 1 ->
    subset (fv A) (support Γ) ->
    [[ Θ; Γ ⊨ t1 ≡ t2 ]] ->
    [[ Θ; Γ ⊨ lambda A t1 ≡ lambda B t2 ]].
Proof.
  intros.
  unshelve epose proof
    (annotated_equivalence_context Θ Γ (lambda A (lvar 1 term_var)) t1 t2 _ _ _ _ _);
    repeat step || list_utils.
Qed.
