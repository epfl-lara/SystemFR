Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.ErasedArrow.

Opaque reducible_values.

Lemma annotated_reducible_lambda:
  forall Θ Γ t U V x,
    ~(x ∈ fv_context Γ) ->
    ~(x ∈ fv t) ->
    ~(x ∈ fv V) ->
    ~(x ∈ Θ) ->
    wf U 0 ->
    wf t 1 ->
    subset (fv_context Γ) (support Γ) ->
    subset (fv U) (support Γ) ->
    subset (fv t) (support Γ) ->
    is_annotated_term t ->
    is_annotated_type V ->
    [[ Θ; (x,U) :: Γ ⊨ open 0 t (fvar x term_var): open 0 V (fvar x term_var) ]] ->
    [[ Θ; Γ ⊨ lambda U t: T_arrow U V ]].
Proof.
  intros; apply open_reducible_lambda with x;
    steps;
    erase_open;
    side_conditions.
Qed.

Lemma annotated_reducible_app:
  forall Θ Γ t1 t2 U V,
    is_annotated_type V ->
    is_annotated_term t2 ->
    wf V 1 ->
    subset (fv V) (support Γ) ->
    [[ Θ; Γ ⊨ t1 : T_arrow U V ]] ->
    [[ Θ; Γ ⊨ t2 : U ]] ->
    [[ Θ; Γ ⊨ app t1 t2 : open 0 V t2 ]].
Proof.
  intros; erase_open.
  apply open_reducible_app with (erase_type U);
    side_conditions.
Qed.
