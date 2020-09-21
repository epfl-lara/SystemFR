Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.ErasedQuant.

Lemma annotated_reducible_forall_inst:
  forall Θ Γ t1 t2 U V,
    is_annotated_type V ->
    is_annotated_term t2 ->
    wf t1 0 ->
    wf t2 0 ->
    wf V 1 ->
    subset (fv t1) (support Γ) ->
    subset (fv t2) (support Γ) ->
    subset (fv V) (support Γ) ->
    [[ Θ; Γ ⊨ t1 : T_forall U V ]] ->
    [[ Θ; Γ ⊨ t2 : U ]] ->
    [[ Θ; Γ ⊨ forall_inst t1 t2 : open 0 V t2 ]].
Proof.
  intros.
  rewrite erase_type_open; steps.
  apply open_reducible_forall_inst with (erase_type U); steps; side_conditions.
Qed.

Lemma annotated_reducible_forall:
  forall Θ Γ t A U V x,
    ~(x ∈ fv_context Γ) ->
    ~(x ∈ fv U) ->
    ~(x ∈ fv V) ->
    ~(x ∈ fv t) ->
    ~(x ∈ Θ) ->
    wf U 0 ->
    subset (fv U) (support Γ) ->
    subset (fv t) (support Γ) ->
    is_annotated_type V ->
    [[ Θ; (x,U) :: Γ ⊨ t : open 0 V (fvar x term_var) ]] ->
    [[ Θ; Γ ⊨ t : A ]] ->
    [[ Θ; Γ ⊨ t : T_forall U V ]].
Proof.
  intros; apply open_reducible_forall with x (erase_type A);
    repeat step || erase_open;
    side_conditions.
Qed.

Lemma annotated_reducible_exists_elim:
  forall Θ Γ p U V x y t T,
    ~(x ∈ fv_context Γ) ->
    ~(y ∈ fv_context Γ) ->
    ~(x = y) ->
    ~(x ∈ fv t) ->
    ~(y ∈ fv t) ->
    ~(x ∈ fv T) ->
    ~(y ∈ fv T) ->
    ~(x ∈ Θ) ->
    ~(y ∈ Θ) ->
    ~(x ∈ fv U) ->
    ~(x ∈ fv V) ->
    ~(y ∈ fv U) ->
    ~(y ∈ fv V) ->
    wf T 0 ->
    wf U 0 ->
    wf V 1 ->
    wf t 1 ->
    subset (fv U) (support Γ) ->
    subset (fv V) (support Γ) ->
    subset (fv T) (support Γ) ->
    subset (fv t) (support Γ) ->
    is_annotated_term t ->
    is_annotated_type V ->
    [[ Θ; Γ ⊨ p : T_exists U V ]] ->
    [[ Θ; (y, open 0 V (fvar x term_var)) :: (x, U) :: Γ ⊨ open 0 t (fvar y term_var) : T ]] ->
    [[ Θ; Γ ⊨ tlet p (T_exists U V) t : T ]].
Proof.
  intros; apply open_reducible_exists_elim with (erase_type U) (erase_type V) x y;
    repeat step || erase_open;
    side_conditions.
Qed.
