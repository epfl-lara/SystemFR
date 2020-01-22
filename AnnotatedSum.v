Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.ErasedSum.

Lemma annotated_reducible_left:
  forall tvars gamma t A B,
    [[ tvars; gamma ⊨ t : A ]] ->
    [[ tvars; gamma ⊨ tleft t : T_sum A B ]].
Proof.
  unfold annotated_reducible;
    repeat step;
    eauto using open_reducible_left.
Qed.

Lemma annotated_reducible_right:
  forall tvars gamma t A B,
    [[ tvars; gamma ⊨ t : B ]] ->
    [[ tvars; gamma ⊨ tright t : T_sum A B ]].
Proof.
  unfold annotated_reducible;
    repeat step;
    eauto using open_reducible_right.
Qed.


Lemma annotated_reducible_sum_match:
  forall tvars gamma t tl tr A B T y p,
    ~(p ∈ fv tl) ->
    ~(p ∈ fv tr) ->
    ~(p ∈ fv t) ->
    ~(p ∈ fv T) ->
    ~(p ∈ fv A) ->
    ~(p ∈ fv B) ->
    ~(p ∈ fv_context gamma) ->
    ~(y ∈ fv tl) ->
    ~(y ∈ fv tr) ->
    ~(y ∈ fv t) ->
    ~(y ∈ fv T) ->
    ~(y ∈ fv A) ->
    ~(y ∈ fv B) ->
    ~(y ∈ fv_context gamma) ->
    ~(y = p) ->
    ~(y ∈ tvars) ->
    ~(p ∈ tvars) ->
    wf T 1 ->
    wf t 0 ->
    wf A 0 ->
    wf B 0 ->
    wf tl 1 ->
    wf tr 1 ->
    is_annotated_type T ->
    is_annotated_term t ->
    is_annotated_term tl ->
    is_annotated_term tr ->
    subset (fv t) (support gamma) ->
    subset (fv tl) (support gamma) ->
    subset (fv tr) (support gamma) ->
    subset (fv A) (support gamma) ->
    subset (fv B) (support gamma) ->
    subset (fv T) (support gamma) ->
    [[ tvars; gamma ⊨ t : T_sum A B ]] ->
    [[
      tvars; (p, T_equiv t (tleft (fvar y term_var))) :: (y, A) :: gamma ⊨
        open 0 tl (fvar y term_var) :
        open 0 T (tleft (fvar y term_var)) ]]
    ->
    [[
      tvars; (p, T_equiv t (tright (fvar y term_var))) :: (y, B) :: gamma ⊨
        open 0 tr (fvar y term_var) :
        open 0 T (tright (fvar y term_var)) ]]
    ->
    [[ tvars; gamma ⊨ sum_match t tl tr : open 0 T t ]].
Proof.
  unfold annotated_reducible; repeat step || erase_open.
  apply open_reducible_sum_match with (erase_type A) (erase_type B) y p;
    repeat step;
    side_conditions.
Qed.
