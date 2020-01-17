Require Import Coq.Lists.List.

Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.ErasedRecognizers.

Lemma annotated_reducible_is_pair:
  forall tvars gamma t,
    [[ tvars; gamma ⊨ t : T_top ]] ->
    [[ tvars; gamma ⊨ boolean_recognizer 0 t : T_bool ]].
Proof.
  unfold annotated_reducible; steps; eauto using open_reducible_is_pair.
Qed.

Lemma annotated_reducible_is_succ:
  forall tvars gamma t,
    [[ tvars; gamma ⊨ t : T_top ]] ->
    [[ tvars; gamma ⊨ boolean_recognizer 1 t : T_bool ]].
Proof.
  unfold annotated_reducible; steps; eauto using open_reducible_is_succ.
Qed.

Lemma annotated_reducible_is_lambda:
  forall tvars gamma t,
    [[ tvars; gamma ⊨ t : T_top ]] ->
    [[ tvars; gamma ⊨ boolean_recognizer 2 t : T_bool ]].
Proof.
  unfold annotated_reducible; steps; eauto using open_reducible_is_lambda.
Qed.
