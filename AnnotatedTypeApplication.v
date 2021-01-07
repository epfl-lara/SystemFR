Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.ErasedTypeApplication.

Lemma annotated_type_application:
  forall tvars gamma f t A B C,
    wf A 0 ->
    wf B 1 ->
    wf C 0 ->
    is_annotated_type A ->
    is_annotated_type B ->
    is_annotated_type C ->
    subset (fv A) (support gamma) ->
    subset (fv B) (support gamma) ->
    subset (fv C) (support gamma) ->
    [[ tvars; gamma ⊨ f : T_arrow A B ]] ->
    [[ tvars; gamma ⊨ t : C ]] ->
    [[ tvars; gamma ⊨ C <: A ]] ->
    [[ tvars; gamma ⊨ app f t : type_application (T_arrow A B) C ]].
Proof.
  repeat step; apply open_reducible_type_application;
    side_conditions.
Qed.
