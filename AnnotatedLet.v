Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.ErasedLet.

Lemma annotated_reducible_let:
  forall tvars gamma t1 t2 x p A B,
    ~(x ∈ fv_context gamma) ->
    ~(p ∈ fv_context gamma) ->
    ~(x = p) ->
    ~(x ∈ fv t2) ->
    ~(p ∈ fv t2) ->
    ~(x ∈ fv B) ->
    ~(p ∈ fv B) ->
    ~(x ∈ fv A) ->
    ~(p ∈ fv A) ->
    ~(x ∈ tvars) ->
    ~(p ∈ tvars) ->
    ~(x ∈ fv t1) ->
    ~(p ∈ fv t1) ->
    wf B 1 ->
    wf t2 1 ->
    is_annotated_type B ->
    is_annotated_term t1 ->
    is_annotated_term t2 ->
    subset (fv t2) (support gamma) ->
    subset (fv A) (support gamma) ->
    subset (fv B) (support gamma) ->
    [[ tvars; gamma ⊨ t1 : A ]] ->
    [[ tvars; (p,T_equiv (term_fvar x) t1) :: (x,A) :: gamma ⊨ open 0 t2 (term_fvar x) : open 0 B (term_fvar x) ]] ->
    [[ tvars; gamma ⊨ tlet t1 A t2 : open 0 B t1 ]].
Proof.
  unfold annotated_reducible;
    repeat step || erase_open.

  apply open_reducible_let with (erase_type A) x p;
    repeat step;
    side_conditions.
Qed.
