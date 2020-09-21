Require Export SystemFR.ErasedSetOps.
Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.

Lemma annotated_reducible_intersection:
  forall Θ Γ t T1 T2,
    [[ Θ; Γ ⊨ t : T1 ]] ->
    [[ Θ; Γ ⊨ t : T2 ]] ->
    [[ Θ; Γ ⊨ t : T_intersection T1 T2 ]].
Proof.
  intros; eauto using open_reducible_intersection.
Qed.

Lemma annotated_reducible_union_elim:
  forall Θ Γ t t' T1 T2 T z,
    ~(z ∈ fv_context Γ) ->
    ~(z ∈ fv t') ->
    ~(z ∈ fv T) ->
    ~(z ∈ fv T1) ->
    ~(z ∈ fv T2) ->
    ~(z ∈ Θ) ->
    subset (fv t') (support Γ) ->
    subset (fv T1) (support Γ) ->
    subset (fv T2) (support Γ) ->
    subset (fv T) (support Γ) ->
    wf t' 1 ->
    wf T1 0 ->
    wf T2 0 ->
    wf T 0 ->
    is_annotated_term t' ->
    [[ Θ; Γ ⊨ t : T_union T1 T2 ]] ->
    [[ Θ; (z,T1) :: Γ ⊨ open 0 t' (fvar z term_var) : T ]] ->
    [[ Θ; (z,T2) :: Γ ⊨ open 0 t' (fvar z term_var) : T ]] ->
    [[ Θ; Γ ⊨ tlet t (T_union T1 T2) t' : T ]].
Proof.
  intros; apply open_reducible_union_elim with (erase_type T1) (erase_type T2) z;
    repeat step || erase_open;
    side_conditions.
Qed.
