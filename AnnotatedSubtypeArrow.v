Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.ErasedSubtype.

Opaque reducible_values.

Lemma annotated_subtype_arrow:
  forall Θ Γ A1 A2 B1 B2 x,
    ~(x ∈ fv_context Γ) ->
    ~(x ∈ fv A2) ->
    ~(x ∈ fv B2) ->
    ~(x ∈ fv B1) ->
    ~(x ∈ Θ) ->
    is_annotated_type A2 ->
    is_annotated_type B2 ->
    [[ Θ; Γ ⊨ B1 <: A1 ]] ->
    [[ Θ; (x,B1) :: Γ ⊨ open 0 A2 (fvar x term_var) <: open 0 B2 (fvar x term_var) ]] ->
    [[ Θ; Γ ⊨ T_arrow A1 A2 <: T_arrow B1 B2 ]].
Proof.
  unfold open_subtype;
    repeat step.
  apply reducible_arrow_subtype_subst with (erase_type A1) (erase_type A2) (erase_context Γ) x;
    repeat step;
    side_conditions.

  unshelve epose proof (H7 ρ l0 _ _ _ v0 _);
    repeat step || erase_open.
Qed.

Lemma annotated_subtype_arrow2:
  forall Θ Γ T A B x f,
    ~(x ∈ fv_context Γ) ->
    ~(f ∈ fv_context Γ) ->
    ~(x = f) ->
    ~(x ∈ fv B) ->
    ~(f ∈ fv B) ->
    ~(x ∈ fv A) ->
    ~(f ∈ fv A) ->
    ~(x ∈ fv T) ->
    ~(f ∈ fv T) ->
    ~(x ∈ Θ) ->
    ~(f ∈ Θ) ->
    is_annotated_type B ->
    [[ Θ; (x,A) :: (f,T) :: Γ ⊨
         app (fvar f term_var) (fvar x term_var) : open 0 B (fvar x term_var) ]] ->
    [[ Θ; Γ ⊨ T <: T_arrow A B ]].
Proof.
  unfold open_subtype;
    repeat step.

  apply subtype_arrow2 with (support ρ) x f (erase_context Γ) (erase_type T);
    repeat step || erase_open;
    side_conditions.
Qed.
