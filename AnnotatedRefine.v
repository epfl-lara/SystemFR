Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.ErasedRefine.

Lemma annotated_reducible_refine:
  forall Θ Γ t A b x p,
    ~(p ∈ fv_context Γ) ->
    ~(p ∈ fv b) ->
    ~(p ∈ fv t) ->
    ~(p ∈ fv A) ->
    ~(x ∈ fv_context Γ) ->
    ~(x ∈ fv b) ->
    ~(x ∈ fv t) ->
    ~(x ∈ fv A) ->
    ~(x = p) ->
    ~(x ∈ Θ) ->
    ~(p ∈ Θ) ->
    wf t 0 ->
    wf b 1 ->
    is_annotated_term b ->
    subset (fv t) (support Γ) ->
    subset (fv b) (support Γ) ->
    [[ Θ; Γ ⊨ t : A ]] ->
    [[ Θ; (x,A) :: Γ ⊨ open 0 b (fvar x term_var) : T_bool ]] ->
    [[ Θ; (p, T_equiv (fvar x term_var) t) :: (x,A) :: Γ ⊨ open 0 b (fvar x term_var) ≡ ttrue ]] ->
    [[ Θ; Γ ⊨ t : T_refine A b ]].
Proof.
  unfold open_equivalent;
    repeat step.
  apply open_reducible_refine with x p;
    repeat step || t_instantiate_sat3 || erase_open;
    side_conditions.
Qed.
