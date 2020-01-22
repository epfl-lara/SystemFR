Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.ErasedQuant.

Lemma annotated_reducible_forall_inst:
  forall tvars gamma t1 t2 U V,
    is_annotated_type V ->
    is_annotated_term t2 ->
    wf t1 0 ->
    wf t2 0 ->
    wf V 1 ->
    subset (fv t1) (support gamma) ->
    subset (fv t2) (support gamma) ->
    subset (fv V) (support gamma) ->
    [[ tvars; gamma ⊨ t1 : T_forall U V ]] ->
    [[ tvars; gamma ⊨ t2 : U ]] ->
    [[ tvars; gamma ⊨ forall_inst t1 t2 : open 0 V t2 ]].
Proof.
  unfold annotated_reducible; intros.
  rewrite erase_type_open; steps.
  apply open_reducible_forall_inst with (erase_type U); steps; side_conditions.
Qed.

Lemma annotated_reducible_forall:
  forall tvars gamma t A U V x,
    ~(x ∈ fv_context gamma) ->
    ~(x ∈ fv U) ->
    ~(x ∈ fv V) ->
    ~(x ∈ fv t) ->
    ~(x ∈ tvars) ->
    wf U 0 ->
    subset (fv U) (support gamma) ->
    subset (fv t) (support gamma) ->
    is_annotated_type V ->
    [[ tvars; (x,U) :: gamma ⊨ t : open 0 V (term_fvar x) ]] ->
    [[ tvars; gamma ⊨ t : A ]] ->
    [[ tvars; gamma ⊨ t : T_forall U V ]].
Proof.
  unfold annotated_reducible;
    repeat step.
  apply open_reducible_forall with x (erase_type A);
    repeat step || erase_open;
    side_conditions.
Qed.

Lemma annotated_reducible_exists_elim:
  forall tvars gamma p U V x y t T,
    ~(x ∈ fv_context gamma) ->
    ~(y ∈ fv_context gamma) ->
    ~(x = y) ->
    ~(x ∈ fv t) ->
    ~(y ∈ fv t) ->
    ~(x ∈ fv T) ->
    ~(y ∈ fv T) ->
    ~(x ∈ tvars) ->
    ~(y ∈ tvars) ->
    ~(x ∈ fv U) ->
    ~(x ∈ fv V) ->
    ~(y ∈ fv U) ->
    ~(y ∈ fv V) ->
    wf T 0 ->
    wf U 0 ->
    wf V 1 ->
    wf t 1 ->
    subset (fv U) (support gamma) ->
    subset (fv V) (support gamma) ->
    subset (fv T) (support gamma) ->
    subset (fv t) (support gamma) ->
    is_annotated_term t ->
    is_annotated_type V ->
    [[ tvars; gamma ⊨ p : T_exists U V ]] ->
    [[ tvars; (y, open 0 V (term_fvar x)) :: (x, U) :: gamma ⊨ open 0 t (term_fvar y) : T ]] ->
    [[ tvars; gamma ⊨ tlet p (T_exists U V) t : T ]].
Proof.
  unfold annotated_reducible;
    repeat step.
  apply open_reducible_exists_elim with (erase_type U) (erase_type V) x y;
    repeat step || erase_open;
    side_conditions.
Qed.
