Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.ErasedSubtype.

Lemma annotated_subtype_prod:
  forall Θ Γ A1 A2 B1 B2 x,
    ~(x ∈ fv_context Γ) ->
    ~(x ∈ fv A1) ->
    ~(x ∈ fv A2) ->
    ~(x ∈ fv B1) ->
    ~(x ∈ fv B2) ->
    ~(x ∈ Θ) ->
    is_annotated_type A2 ->
    is_annotated_type B2 ->
    [[ Θ; Γ ⊨ A1 <: B1 ]] ->
    [[ Θ; (x,A1) :: Γ ⊨ open 0 A2 (fvar x term_var) <: open 0 B2 (fvar x term_var) ]] ->
    [[ Θ; Γ ⊨ T_prod A1 A2 <: T_prod B1 B2 ]].
Proof.
  unfold open_subtype;
    repeat step.
  apply reducible_prod_subtype_subst with (erase_type A1) (erase_type A2) x (erase_context Γ);
    repeat step;
    side_conditions.

  unshelve epose proof (H8 ρ l0 _ _ _ v0 _);
    repeat step || erase_open.
Qed.

Lemma annotated_subtype_prod2:
  forall Θ Γ T A B x,
    ~(x ∈ fv_context Γ) ->
    ~(x ∈ fv B) ->
    ~(x ∈ fv A) ->
    ~(x ∈ fv T) ->
    ~(x ∈ Θ) ->
    is_annotated_type B ->
    wf B 1 ->
    subset (fv B) (support Γ) ->
    [[ Θ; (x,T) :: Γ ⊨ pi1 (fvar x term_var) : A ]] ->
    [[ Θ; (x,T) :: Γ ⊨ pi2 (fvar x term_var) : open 0 B (pi1 (fvar x term_var)) ]] ->
    [[ Θ; Γ ⊨ T  <: T_prod A B ]].
Proof.
  unfold open_subtype; repeat step.

  apply subtype_prod2 with (erase_context Γ) (erase_type T) x;
    repeat step || erase_open;
    side_conditions.
Qed.
