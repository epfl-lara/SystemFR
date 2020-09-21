Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.ErasedSubtypeQuant.

Opaque reducible_values.

Lemma annotated_subtype_bot:
  forall Θ Γ T,
    [[ Θ; Γ ⊨ T_bot <: T ]].
Proof.
  unfold open_subtype;
    repeat step || simp_red.
Qed.

Lemma annotated_subtype_top:
  forall Θ Γ T,
    [[ Θ; Γ ⊨ T <: T_top ]].
Proof.
  unfold open_subtype;
    repeat step || simp_red;
    eauto using reducible_values_closed.
Qed.

Lemma annotated_subtype_intersection1:
  forall Θ Γ T1 T2,
    [[ Θ; Γ ⊨ T_intersection T1 T2 <: T1 ]].
Proof.
  unfold open_subtype;
    repeat step || simp_red.
Qed.

Lemma annotated_subtype_intersection2:
  forall Θ Γ T1 T2,
    [[ Θ; Γ ⊨ T_intersection T1 T2 <: T2 ]].
Proof.
  unfold open_subtype;
    repeat step || simp_red.
Qed.

Lemma annotated_subtype_union1:
  forall Θ Γ T1 T2,
    [[ Θ; Γ ⊨ T1 <: T_union T1 T2 ]].
Proof.
  unfold open_subtype;
    repeat step || simp_red;
    eauto using reducible_values_closed.
Qed.

Lemma annotated_subtype_union2:
  forall Θ Γ T1 T2,
    [[ Θ; Γ ⊨ T2 <: T_union T1 T2 ]].
Proof.
  unfold open_subtype;
    repeat step || simp_red;
    eauto using reducible_values_closed.
Qed.

Lemma annotated_subtype_forall:
  forall Θ Γ t T1 T2 x,
    ~(x ∈ support Γ) ->
    ~(x ∈ fv T2) ->
    ~(x ∈ Θ) ->
    is_annotated_type T2 ->
    is_annotated_term t ->
    wf T2 1 ->
    subset (fv T2) (support Γ) ->
    [[ Θ; Γ ⊨ t : T1 ]] ->
    [[ Θ; Γ ⊨ T_forall T1 T2 <: open 0 T2 t ]].
Proof.
  unfold open_subtype;
    repeat step || t_substitutions || erase_open.

  eapply subtype_forall; steps; try eassumption;
    repeat step;
    side_conditions.
Qed.

Lemma annotated_subtype_exists:
  forall Θ Γ t T1 T2 x,
    ~(x ∈ support Γ) ->
    ~(x ∈ fv T2) ->
    ~(x ∈ Θ) ->
    is_annotated_type T2 ->
    is_annotated_term t ->
    wf T2 1 ->
    subset (fv T2) (support Γ) ->
    [[ Θ; Γ ⊨ t : T1 ]] ->
    [[ Θ; Γ ⊨ open 0 T2 t <: T_exists T1 T2 ]].
  unfold open_subtype;
    repeat step || t_substitutions || erase_open.

  eapply subtype_exists; steps; try eassumption;
    repeat step;
    side_conditions.
Qed.
