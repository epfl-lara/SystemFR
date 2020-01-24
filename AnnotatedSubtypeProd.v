Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.ErasedSubtype.

Lemma annotated_subtype_prod:
  forall tvars gamma A1 A2 B1 B2 x,
    ~(x ∈ fv_context gamma) ->
    ~(x ∈ fv A1) ->
    ~(x ∈ fv A2) ->
    ~(x ∈ fv B1) ->
    ~(x ∈ fv B2) ->
    ~(x ∈ tvars) ->
    is_annotated_type A2 ->
    is_annotated_type B2 ->
    [[ tvars; gamma ⊨ A1 <: B1 ]] ->
    [[ tvars; (x,A1) :: gamma ⊨ open 0 A2 (fvar x term_var) <: open 0 B2 (fvar x term_var) ]] ->
    [[ tvars; gamma ⊨ T_prod A1 A2 <: T_prod B1 B2 ]].
Proof.
  unfold annotated_subtype, subtype;
    repeat step.
  apply reducible_prod_subtype_subst with (erase_type A1) (erase_type A2) x (erase_context gamma);
    repeat step;
    side_conditions.

  unshelve epose proof (H8 theta l0 _ _ _ t _);
    repeat step || erase_open.
Qed.

Lemma annotated_subtype_prod2:
  forall tvars gamma T A B x,
    ~(x ∈ fv_context gamma) ->
    ~(x ∈ fv B) ->
    ~(x ∈ fv A) ->
    ~(x ∈ fv T) ->
    ~(x ∈ tvars) ->
    is_annotated_type B ->
    wf B 1 ->
    subset (fv B) (support gamma) ->
    [[ tvars; (x,T) :: gamma ⊨ pi1 (fvar x term_var) : A ]] ->
    [[ tvars; (x,T) :: gamma ⊨ pi2 (fvar x term_var) : open 0 B (pi1 (fvar x term_var)) ]] ->
    [[ tvars; gamma ⊨ T  <: T_prod A B ]].
Proof.
  unfold annotated_reducible, annotated_subtype, subtype;
    repeat step.

  apply subtype_prod2 with (erase_context gamma) (erase_type T) x;
    repeat step || erase_open;
    side_conditions.
Qed.
