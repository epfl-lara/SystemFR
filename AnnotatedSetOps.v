Require Export SystemFR.ErasedSetOps.
Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.

Lemma annotated_reducible_intersection:
  forall tvars gamma t T1 T2,
    [[ tvars; gamma ⊨ t : T1 ]] ->
    [[ tvars; gamma ⊨ t : T2 ]] ->
    [[ tvars; gamma ⊨ t : T_intersection T1 T2 ]].
Proof.
  unfold annotated_reducible;
    repeat step;
    eauto using open_reducible_intersection.
Qed.

Lemma annotated_reducible_union_elim:
  forall tvars gamma t t' T1 T2 T z,
    ~(z ∈ fv_context gamma) ->
    ~(z ∈ fv t') ->
    ~(z ∈ fv T) ->
    ~(z ∈ fv T1) ->
    ~(z ∈ fv T2) ->
    ~(z ∈ tvars) ->
    subset (fv t') (support gamma) ->
    subset (fv T1) (support gamma) ->
    subset (fv T2) (support gamma) ->
    subset (fv T) (support gamma) ->
    wf t' 1 ->
    wf T1 0 ->
    wf T2 0 ->
    wf T 0 ->
    is_annotated_term t' ->
    [[ tvars; gamma ⊨ t : T_union T1 T2 ]] ->
    [[ tvars; (z,T1) :: gamma ⊨ open 0 t' (term_fvar z) : T ]] ->
    [[ tvars; (z,T2) :: gamma ⊨ open 0 t' (term_fvar z) : T ]] ->
    [[ tvars; gamma ⊨ tlet t (T_union T1 T2) t' : T ]].
Proof.
  unfold annotated_reducible;
    repeat step.
  apply open_reducible_union_elim with (erase_type T1) (erase_type T2) z;
    repeat step || erase_open;
    side_conditions.
Qed.
