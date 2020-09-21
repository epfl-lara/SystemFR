Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.ErasedLet.


Lemma annotated_reducible_let:
  forall Θ Γ t1 t2 x p A B,
    ~(x ∈ fv_context Γ) ->
    ~(p ∈ fv_context Γ) ->
    ~(x = p) ->
    ~(x ∈ fv t2) ->
    ~(p ∈ fv t2) ->
    ~(x ∈ fv B) ->
    ~(p ∈ fv B) ->
    ~(x ∈ fv A) ->
    ~(p ∈ fv A) ->
    ~(x ∈ Θ) ->
    ~(p ∈ Θ) ->
    ~(x ∈ fv t1) ->
    ~(p ∈ fv t1) ->
    wf B 1 ->
    wf t2 1 ->
    is_annotated_type B ->
    is_annotated_term t1 ->
    is_annotated_term t2 ->
    subset (fv t2) (support Γ) ->
    subset (fv A) (support Γ) ->
    subset (fv B) (support Γ) ->
    [[ Θ; Γ ⊨ t1 : A ]] ->
    [[ Θ; (p,T_equiv (fvar x term_var) t1) :: (x,A) :: Γ ⊨ open 0 t2 (fvar x term_var) : open 0 B (fvar x term_var) ]] ->
    [[ Θ; Γ ⊨ tlet t1 A t2 : open 0 B t1 ]].
Proof.
  repeat step || erase_open.

  apply open_reducible_let with (erase_type A) x p;
    repeat step;
    side_conditions.
Qed.
