Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.ErasedSubtypeQuant.

Opaque reducible_values.

Lemma annotated_subtype_bot:
  forall tvars gamma T,
    [[ tvars; gamma ⊨ T_bot <: T ]].
Proof.
  unfold annotated_subtype, open_subtype, subtype;
    repeat step || simp_red.
Qed.

Lemma annotated_subtype_top:
  forall tvars gamma T,
    [[ tvars; gamma ⊨ T <: T_top ]].
Proof.
  unfold annotated_subtype, open_subtype, subtype;
    repeat step || simp_red;
    eauto using reducible_values_closed.
Qed.

Lemma annotated_subtype_intersection1:
  forall tvars gamma T1 T2,
    [[ tvars; gamma ⊨ T_intersection T1 T2 <: T1 ]].
Proof.
  unfold annotated_subtype, open_subtype, subtype;
    repeat step || simp_red.
Qed.

Lemma annotated_subtype_intersection2:
  forall tvars gamma T1 T2,
    [[ tvars; gamma ⊨ T_intersection T1 T2 <: T2 ]].
Proof.
  unfold annotated_subtype, open_subtype, subtype;
    repeat step || simp_red.
Qed.

Lemma annotated_subtype_union1:
  forall tvars gamma T1 T2,
    [[ tvars; gamma ⊨ T1 <: T_union T1 T2 ]].
Proof.
  unfold annotated_subtype, open_subtype, subtype;
    repeat step || simp_red;
    eauto using reducible_values_closed.
Qed.

Lemma annotated_subtype_union2:
  forall tvars gamma T1 T2,
    [[ tvars; gamma ⊨ T2 <: T_union T1 T2 ]].
Proof.
  unfold annotated_subtype, open_subtype, subtype;
    repeat step || simp_red;
    eauto using reducible_values_closed.
Qed.

Lemma annotated_subtype_forall:
  forall tvars gamma t T1 T2 x,
    ~(x ∈ support gamma) ->
    ~(x ∈ fv T2) ->
    ~(x ∈ tvars) ->
    is_annotated_type T2 ->
    is_annotated_term t ->
    wf T2 1 ->
    subset (fv T2) (support gamma) ->
    [[ tvars; gamma ⊨ t : T1 ]] ->
    [[ tvars; gamma ⊨ T_forall T1 T2 <: open 0 T2 t ]].
Proof.
  unfold annotated_subtype, open_subtype, subtype, annotated_reducible;
    repeat step || t_substitutions || erase_open.

  eapply subtype_forall; steps; try eassumption;
    repeat step;
    side_conditions.
Qed.

Lemma annotated_subtype_exists:
  forall tvars gamma t T1 T2 x,
    ~(x ∈ support gamma) ->
    ~(x ∈ fv T2) ->
    ~(x ∈ tvars) ->
    is_annotated_type T2 ->
    is_annotated_term t ->
    wf T2 1 ->
    subset (fv T2) (support gamma) ->
    [[ tvars; gamma ⊨ t : T1 ]] ->
    [[ tvars; gamma ⊨ open 0 T2 t <: T_exists T1 T2 ]].
  unfold annotated_subtype, open_subtype, subtype, annotated_reducible;
    repeat step || t_substitutions || erase_open.

  eapply subtype_exists; steps; try eassumption;
    repeat step;
    side_conditions.
Qed.
