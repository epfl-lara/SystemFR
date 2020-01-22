Require Export SystemFR.Judgments.
Require Export SystemFR.TypeErasureLemmas.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.ErasedPolymorphism.

Lemma annotated_reducible_type_abs:
  forall tvars gamma t T X,
    ~(X ∈ pfv_context gamma term_var) ->
    ~(X ∈ pfv_context gamma type_var) ->
    ~(X ∈ pfv t term_var) ->
    ~(X ∈ pfv T term_var) ->
    ~(X ∈ pfv T type_var) ->
    ~(X ∈ tvars) ->
    subset (fv t) (support gamma) ->
    subset (fv T) (support gamma) ->
    wf t 0 ->
    wf T 1 ->
    twf t 0 ->
    is_annotated_type T ->
    [[ X :: tvars; gamma ⊨ topen 0 t (type_fvar X) : topen 0 T (type_fvar X) ]] ->
    [[ tvars; gamma ⊨ type_abs t : T_abs T ]].
Proof.
  unfold annotated_reducible; intros.
  apply open_reducible_type_abs with X;
    repeat step ||
           (rewrite erase_type_topen in * by steps) ||
           (rewrite topen_none in * by auto);
    side_conditions.
Qed.

Lemma annotated_reducible_type_inst:
  forall tvars gamma t U V,
    is_annotated_type U ->
    is_annotated_type V ->
    wf U 0 ->
    wf V 0 ->
    twf V 0 ->
    subset (fv U) (support gamma) ->
    subset (fv V) (support gamma) ->
    [[ tvars; gamma ⊨ t : T_abs U ]] ->
    [[ tvars; gamma ⊨ type_inst t V : topen 0 U V ]].
Proof.
  unfold annotated_reducible; intros.
  rewrite erase_type_topen; steps.
  apply open_reducible_inst; steps; side_conditions.
Qed.
