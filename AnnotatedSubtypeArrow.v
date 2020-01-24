Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.ErasedSubtype.

Opaque reducible_values.

Lemma annotated_subtype_arrow:
  forall tvars gamma A1 A2 B1 B2 x,
    ~(x ∈ fv_context gamma) ->
    ~(x ∈ fv A2) ->
    ~(x ∈ fv B2) ->
    ~(x ∈ fv B1) ->
    ~(x ∈ tvars) ->
    is_annotated_type A2 ->
    is_annotated_type B2 ->
    [[ tvars; gamma ⊨ B1 <: A1 ]] ->
    [[ tvars; (x,B1) :: gamma ⊨ open 0 A2 (fvar x term_var) <: open 0 B2 (fvar x term_var) ]] ->
    [[ tvars; gamma ⊨ T_arrow A1 A2 <: T_arrow B1 B2 ]].
Proof.
  unfold annotated_subtype, subtype;
    repeat step.
  apply reducible_arrow_subtype_subst with (erase_type A1) (erase_type A2) (erase_context gamma) x;
    repeat step;
    side_conditions.

  unshelve epose proof (H7 theta l0 _ _ _ t _);
    repeat step || erase_open.
Qed.

Lemma annotated_subtype_arrow2:
  forall tvars gamma T A B x f,
    ~(x ∈ fv_context gamma) ->
    ~(f ∈ fv_context gamma) ->
    ~(x = f) ->
    ~(x ∈ fv B) ->
    ~(f ∈ fv B) ->
    ~(x ∈ fv A) ->
    ~(f ∈ fv A) ->
    ~(x ∈ fv T) ->
    ~(f ∈ fv T) ->
    ~(x ∈ tvars) ->
    ~(f ∈ tvars) ->
    is_annotated_type B ->
    [[ tvars; (x,A) :: (f,T) :: gamma ⊨
         app (fvar f term_var) (fvar x term_var) : open 0 B (fvar x term_var) ]] ->
    [[ tvars; gamma ⊨ T <: T_arrow A B ]].
Proof.
  unfold annotated_reducible, annotated_subtype, subtype;
    repeat step.

  apply subtype_arrow2 with (support theta) x f (erase_context gamma) (erase_type T);
    repeat step || erase_open;
    side_conditions.
Qed.
