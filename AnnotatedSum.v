Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.ErasedSum.

Lemma annotated_reducible_left:
  forall Θ Γ t A B,
    [[ Θ; Γ ⊨ t : A ]] ->
    [[ Θ; Γ ⊨ tleft t : T_sum A B ]].
Proof.
  intros; eauto using open_reducible_left.
Qed.

Lemma annotated_reducible_right:
  forall Θ Γ t A B,
    [[ Θ; Γ ⊨ t : B ]] ->
    [[ Θ; Γ ⊨ tright t : T_sum A B ]].
Proof.
  intros; eauto using open_reducible_right.
Qed.

Lemma annotated_reducible_sum_match:
  forall Θ Γ t tl tr A B T y p,
    ~(p ∈ fv tl) ->
    ~(p ∈ fv tr) ->
    ~(p ∈ fv t) ->
    ~(p ∈ fv T) ->
    ~(p ∈ fv A) ->
    ~(p ∈ fv B) ->
    ~(p ∈ fv_context Γ) ->
    ~(y ∈ fv tl) ->
    ~(y ∈ fv tr) ->
    ~(y ∈ fv t) ->
    ~(y ∈ fv T) ->
    ~(y ∈ fv A) ->
    ~(y ∈ fv B) ->
    ~(y ∈ fv_context Γ) ->
    ~(y = p) ->
    ~(y ∈ Θ) ->
    ~(p ∈ Θ) ->
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
    subset (fv t) (support Γ) ->
    subset (fv tl) (support Γ) ->
    subset (fv tr) (support Γ) ->
    subset (fv A) (support Γ) ->
    subset (fv B) (support Γ) ->
    subset (fv T) (support Γ) ->
    [[ Θ; Γ ⊨ t : T_sum A B ]] ->
    [[
      Θ; (p, T_equiv t (tleft (fvar y term_var))) :: (y, A) :: Γ ⊨
        open 0 tl (fvar y term_var) :
        open 0 T (tleft (fvar y term_var)) ]]
    ->
    [[
      Θ; (p, T_equiv t (tright (fvar y term_var))) :: (y, B) :: Γ ⊨
        open 0 tr (fvar y term_var) :
        open 0 T (tright (fvar y term_var)) ]]
    ->
    [[ Θ; Γ ⊨ sum_match t tl tr : open 0 T t ]].
Proof.
  repeat step || erase_open.
  apply open_reducible_sum_match with (erase_type A) (erase_type B) y p;
    repeat step;
    side_conditions.
Qed.
