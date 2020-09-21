Require Export SystemFR.Judgments.
Require Export SystemFR.TypeErasureLemmas.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.ErasedPolymorphism.

Lemma annotated_reducible_type_abs:
  forall Θ Γ t T X,
    ~(X ∈ pfv_context Γ term_var) ->
    ~(X ∈ pfv_context Γ type_var) ->
    ~(X ∈ pfv t term_var) ->
    ~(X ∈ pfv T term_var) ->
    ~(X ∈ pfv T type_var) ->
    ~(X ∈ Θ) ->
    subset (fv t) (support Γ) ->
    subset (fv T) (support Γ) ->
    wf t 0 ->
    wf T 1 ->
    twf t 0 ->
    is_annotated_type T ->
    [[ X :: Θ; Γ ⊨ topen 0 t (fvar X type_var) : topen 0 T (fvar X type_var) ]] ->
    [[ Θ; Γ ⊨ type_abs t : T_abs T ]].
Proof.
  intros.
  apply open_reducible_type_abs with X;
    repeat step ||
           (rewrite erase_type_topen in * by steps) ||
           (rewrite topen_none in * by auto);
    side_conditions.
Qed.

Lemma annotated_reducible_type_inst:
  forall Θ Γ t U V,
    is_annotated_type U ->
    is_annotated_type V ->
    wf U 0 ->
    wf V 0 ->
    twf V 0 ->
    subset (fv U) (support Γ) ->
    subset (fv V) (support Γ) ->
    [[ Θ; Γ ⊨ t : T_abs U ]] ->
    [[ Θ; Γ ⊨ type_inst t V : topen 0 U V ]].
Proof.
  intros.
  rewrite erase_type_topen; steps.
  apply open_reducible_inst; steps; side_conditions.
Qed.
