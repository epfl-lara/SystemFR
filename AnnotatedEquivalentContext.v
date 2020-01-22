Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.RedTactics.
Require Export SystemFR.EquivalentContext.

Lemma annotated_equivalence_context:
  forall tvars gamma C t1 t2,
    wf C 1 ->
    is_annotated_term C ->
    subset (fv C) (support gamma) ->
    is_annotated_term t1 ->
    is_annotated_term t2 ->
    [[ tvars; gamma ⊨ t1 ≡ t2 ]] ->
    [[ tvars; gamma ⊨ open 0 C t1 ≡ open 0 C t2 ]].
Proof.
  unfold annotated_equivalent, equivalent;
    repeat step || erase_open || t_substitutions || apply equivalent_context;
    eauto with erased;
    eauto with wf;
    eauto with fv.
Qed.

Lemma annotated_equivalence_lambdas:
  forall tvars gamma t1 t2 A B,
    is_annotated_term t1 ->
    is_annotated_term t2 ->
    is_annotated_type A ->
    wf A 1 ->
    subset (fv A) (support gamma) ->
    [[ tvars; gamma ⊨ t1 ≡ t2 ]] ->
    [[ tvars; gamma ⊨ lambda A t1 ≡ lambda B t2 ]].
Proof.
  intros.
  unshelve epose proof
    (annotated_equivalence_context tvars gamma (lambda A (lvar 1 term_var)) t1 t2 _ _ _ _ _);
    repeat step || list_utils.
Qed.
