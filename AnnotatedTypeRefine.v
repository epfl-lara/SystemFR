Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.ErasedTypeRefine.

Lemma annotated_reducible_type_refine:
  forall Θ Γ A B t1 t2,
    wf B 1 ->
    is_annotated_type B ->
    is_annotated_term t1 ->
    subset (fv B) (support Γ) ->
    [[ Θ; Γ ⊨ t1 : A ]] ->
    [[ Θ; Γ ⊨ t2 : open 0 B t1 ]] ->
    [[ Θ; Γ ⊨ because t1 t2 : T_type_refine A B ]].
Proof.
  intros.
  eapply open_reducible_type_refine; try eassumption;
    repeat step || erase_open;
    side_conditions.
Qed.

Lemma annotated_reducible_get_refinement_witness:
  forall Θ Γ t1 t2 A B T x,
    ~(x ∈ Θ) ->
    ~(x ∈ fv_context Γ) ->
    ~(x ∈ fv t1) ->
    ~(x ∈ fv t2) ->
    ~(x ∈ fv T) ->
    ~(x ∈ fv A) ->
    ~(x ∈ fv B) ->
    wf t1 0 ->
    wf (erase_term t2) 0 ->
    wf B 1 ->
    subset (fv t1) (support Γ) ->
    subset (fv t2) (support Γ) ->
    subset (fv B) (support Γ) ->
    is_annotated_type B ->
    is_annotated_term t1 ->
    is_annotated_term t2 ->
    [[ Θ; Γ ⊨ t1 : T_type_refine A B ]] ->
    [[ Θ; (x, open 0 B t1) :: Γ ⊨ open 0 t2 (fvar x term_var) : T ]] ->
    [[ Θ; Γ ⊨ get_refinement_witness t1 t2 : T ]].
Proof.
  intros.
  apply open_reducible_get_refinement_witness
    with (erase_term t1) (erase_type A) (erase_type B) x; try eassumption;
    repeat step || erase_open || rewrite (open_none (erase_term t2)) in * by auto;
    side_conditions.
Qed.
