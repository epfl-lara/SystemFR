Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.ErasedRefine.

Lemma annotated_subtype_refine:
  forall tvars gamma A B p q x,
    ~(x ∈ fv_context gamma) ->
    ~(x ∈ fv p) ->
    ~(x ∈ fv q) ->
    ~(x ∈ fv A) ->
    ~(x ∈ tvars) ->
    wf q 1 ->
    is_annotated_term q ->
    subset (fv q) (support gamma) ->
    [[ tvars; (x, T_refine A p) :: gamma ⊨ open 0 q (term_fvar x) ≡ ttrue ]] ->
    [[ tvars; gamma ⊨ A <: B ]] ->
    [[ tvars; gamma ⊨ T_refine A p <: T_refine B q ]].
Proof.
  unfold annotated_equivalent, equivalent, annotated_subtype, subtype;
    repeat step.

  apply subtype_refine with
    (erase_context gamma) (erase_type A) (erase_term p) x;
    repeat step || t_instantiate_sat3 || erase_open;
    side_conditions.
Qed.

Lemma annotated_subtype_refine2:
  forall tvars gamma A B p,
    [[ tvars; gamma ⊨ A <: B ]] ->
    [[ tvars; gamma ⊨ T_refine A p <: B ]].
Proof.
  unfold annotated_equivalent, equivalent, annotated_subtype, subtype;
    repeat step || simp_red.
Qed.

Lemma annotated_subtype_refine3:
  forall tvars gamma A,
    [[ tvars; gamma ⊨ A <: T_refine A ttrue ]].
Proof.
  unfold annotated_equivalent, equivalent, annotated_subtype, subtype;
    repeat step || simp_red;
    t_closer.
Qed.

Lemma annotated_subtype_refine4:
  forall tvars gamma T A p x,
    ~(x ∈ fv_context gamma) ->
    ~(x ∈ fv p) ->
    ~(x ∈ fv T) ->
    ~(x ∈ tvars) ->
    wf p 1 ->
    is_annotated_term p ->
    subset (fv p) (support gamma) ->
    [[ tvars; (x, T) :: gamma ⊨ open 0 p (term_fvar x) ≡ ttrue ]] ->
    [[ tvars; gamma ⊨ T <: A ]] ->
    [[ tvars; gamma ⊨ T <: T_refine A p ]].
Proof.
  unfold annotated_equivalent, equivalent, annotated_subtype, subtype;
    repeat step.

  apply subtype_refine4 with (erase_context gamma) (erase_type T) x;
    repeat step || t_instantiate_sat3 || erase_open;
    side_conditions.
Qed.

Lemma annotated_subtype_refine5:
  forall tvars gamma T A b x p,
    ~(x ∈ fv_context gamma) ->
    ~(p ∈ fv_context gamma) ->
    ~(x = p) ->
    ~(x ∈ fv b) ->
    ~(p ∈ fv b) ->
    ~(x ∈ fv T) ->
    ~(p ∈ fv T) ->
    ~(x ∈ fv A) ->
    ~(p ∈ fv A) ->
    ~(x ∈ tvars) ->
    ~(p ∈ tvars) ->
    is_annotated_term b ->
    [[ tvars; (p, T_equiv (open 0 b (term_fvar x)) ttrue) :: (x, A) :: gamma ⊨ term_fvar x: T ]] ->
    [[ tvars; gamma ⊨ T_refine A b <: T ]].
Proof.
  unfold annotated_equivalent, equivalent, annotated_subtype, subtype, annotated_reducible;
    repeat step.

  apply subtype_refine5 with (erase_context gamma) (erase_type A) (erase_term b) x p;
    repeat step || t_instantiate_sat3 || erase_open;
    side_conditions.
Qed.
