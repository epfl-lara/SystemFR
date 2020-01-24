Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.ErasedArrow.

Opaque reducible_values.

Lemma annotated_reducible_lambda:
  forall tvars gamma t U V x,
    ~(x ∈ fv_context gamma) ->
    ~(x ∈ fv t) ->
    ~(x ∈ fv V) ->
    ~(x ∈ tvars) ->
    wf U 0 ->
    wf t 1 ->
    subset (fv_context gamma) (support gamma) ->
    subset (fv U) (support gamma) ->
    subset (fv t) (support gamma) ->
    is_annotated_term t ->
    is_annotated_type V ->
    [[ tvars; (x,U) :: gamma ⊨ open 0 t (fvar x term_var): open 0 V (fvar x term_var) ]] ->
    [[ tvars; gamma ⊨ lambda U t: T_arrow U V ]].
Proof.
  unfold annotated_reducible; intros.
  apply open_reducible_lambda with x;
    steps;
    erase_open;
    side_conditions.
Qed.

Lemma annotated_reducible_app:
  forall tvars gamma t1 t2 U V,
    is_annotated_type V ->
    is_annotated_term t2 ->
    wf V 1 ->
    subset (fv V) (support gamma) ->
    [[ tvars; gamma ⊨ t1 : T_arrow U V ]] ->
    [[ tvars; gamma ⊨ t2 : U ]] ->
    [[ tvars; gamma ⊨ app t1 t2 : open 0 V t2 ]].
Proof.
  unfold annotated_reducible; intros; erase_open.
  apply open_reducible_app with (erase_type U);
    side_conditions.
Qed.
