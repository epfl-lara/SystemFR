Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.ErasedRefine.

Lemma annotated_reducible_refine:
  forall tvars gamma t A b x p,
    ~(p ∈ fv_context gamma) ->
    ~(p ∈ fv b) ->
    ~(p ∈ fv t) ->
    ~(p ∈ fv A) ->
    ~(x ∈ fv_context gamma) ->
    ~(x ∈ fv b) ->
    ~(x ∈ fv t) ->
    ~(x ∈ fv A) ->
    ~(x = p) ->
    ~(x ∈ tvars) ->
    ~(p ∈ tvars) ->
    wf t 0 ->
    wf b 1 ->
    is_annotated_term b ->
    subset (fv t) (support gamma) ->
    subset (fv b) (support gamma) ->
    [[ tvars; gamma ⊨ t : A ]] ->
    [[ tvars; (x,A) :: gamma ⊨ open 0 b (fvar x term_var) : T_bool ]] ->
    [[ tvars; (p, T_equiv (fvar x term_var) t) :: (x,A) :: gamma ⊨ open 0 b (fvar x term_var) ≡ ttrue ]] ->
    [[ tvars; gamma ⊨ t : T_refine A b ]].
Proof.
  unfold annotated_reducible, annotated_equivalent, open_equivalent;
    repeat step.
  apply open_reducible_refine with x p;
    repeat step || t_instantiate_sat3 || erase_open;
    side_conditions.
Qed.
