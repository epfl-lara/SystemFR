From Stdlib Require Import List.

Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.ErasedRecognizers.

Lemma annotated_reducible_is_pair:
  forall Θ Γ t,
    [[ Θ; Γ ⊨ t : T_top ]] ->
    [[ Θ; Γ ⊨ boolean_recognizer 0 t : T_bool ]].
Proof.
  intros; eauto using open_reducible_is_pair.
Qed.

Lemma annotated_reducible_is_succ:
  forall Θ Γ t,
    [[ Θ; Γ ⊨ t : T_top ]] ->
    [[ Θ; Γ ⊨ boolean_recognizer 1 t : T_bool ]].
Proof.
  intros; eauto using open_reducible_is_succ.
Qed.

Lemma annotated_reducible_is_lambda:
  forall Θ Γ t,
    [[ Θ; Γ ⊨ t : T_top ]] ->
    [[ Θ; Γ ⊨ boolean_recognizer 2 t : T_bool ]].
Proof.
  intros; eauto using open_reducible_is_lambda.
Qed.
