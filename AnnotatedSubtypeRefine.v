Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.ErasedRefine.

Opaque reducible_values.

Lemma annotated_subtype_refine:
  forall Θ Γ A B p q x,
    ~(x ∈ fv_context Γ) ->
    ~(x ∈ fv p) ->
    ~(x ∈ fv q) ->
    ~(x ∈ fv A) ->
    ~(x ∈ Θ) ->
    wf q 1 ->
    is_annotated_term q ->
    subset (fv q) (support Γ) ->
    [[ Θ; (x, T_refine A p) :: Γ ⊨ open 0 q (fvar x term_var) ≡ ttrue ]] ->
    [[ Θ; Γ ⊨ A <: B ]] ->
    [[ Θ; Γ ⊨ T_refine A p <: T_refine B q ]].
Proof.
  unfold open_equivalent, open_subtype;
    repeat step.

  apply subtype_refine with
    (erase_context Γ) (erase_type A) (erase_term p) x;
    repeat step || t_instantiate_sat3 || erase_open;
    side_conditions.
Qed.

Lemma annotated_subtype_refine2:
  forall Θ Γ A B p,
    [[ Θ; Γ ⊨ A <: B ]] ->
    [[ Θ; Γ ⊨ T_refine A p <: B ]].
Proof.
  unfold open_equivalent, open_subtype;
    repeat step || simp_red.
Qed.

Lemma annotated_subtype_refine3:
  forall Θ Γ A,
    [[ Θ; Γ ⊨ A <: T_refine A ttrue ]].
Proof.
  unfold open_equivalent, open_subtype;
    repeat step || simp_red;
    t_closer.
Qed.

Lemma annotated_subtype_refine4:
  forall Θ Γ T A p x,
    ~(x ∈ fv_context Γ) ->
    ~(x ∈ fv p) ->
    ~(x ∈ fv T) ->
    ~(x ∈ Θ) ->
    wf p 1 ->
    is_annotated_term p ->
    subset (fv p) (support Γ) ->
    [[ Θ; (x, T) :: Γ ⊨ open 0 p (fvar x term_var) ≡ ttrue ]] ->
    [[ Θ; Γ ⊨ T <: A ]] ->
    [[ Θ; Γ ⊨ T <: T_refine A p ]].
Proof.
  unfold open_equivalent, open_subtype;
    repeat step.

  apply subtype_refine4 with (erase_context Γ) (erase_type T) x;
    repeat step || t_instantiate_sat3 || erase_open;
    side_conditions.
Qed.

Lemma annotated_subtype_refine5:
  forall Θ Γ T A b x p,
    ~(x ∈ fv_context Γ) ->
    ~(p ∈ fv_context Γ) ->
    ~(x = p) ->
    ~(x ∈ fv b) ->
    ~(p ∈ fv b) ->
    ~(x ∈ fv T) ->
    ~(p ∈ fv T) ->
    ~(x ∈ fv A) ->
    ~(p ∈ fv A) ->
    ~(x ∈ Θ) ->
    ~(p ∈ Θ) ->
    is_annotated_term b ->
    [[ Θ; (p, T_equiv (open 0 b (fvar x term_var)) ttrue) :: (x, A) :: Γ ⊨ fvar x term_var: T ]] ->
    [[ Θ; Γ ⊨ T_refine A b <: T ]].
Proof.
  unfold open_equivalent, open_subtype;
    repeat step.

  apply subtype_refine5 with (erase_context Γ) (erase_type A) (erase_term b) x p;
    repeat step || t_instantiate_sat3 || erase_open;
    side_conditions.
Qed.
