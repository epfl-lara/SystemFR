Require Export SystemFR.ScalaDepSugar.
Require Export SystemFR.SubtypeExists.
Require Export SystemFR.ReducibilitySubtype.

Opaque reducible_values.

Lemma subtype_union_left:
  forall ρ T1 T2 T,
    [ ρ | T1 <: T ] ->
    [ ρ | T2 <: T ] ->
    [ ρ | T_union T1 T2 <: T ].
Proof.
  unfold subtype; repeat step || simp_red.
Qed.

Lemma open_subtype_union_left:
  forall Θ Γ T1 T2 T,
    [ Θ; Γ ⊨ T1 <: T ] ->
    [ Θ; Γ ⊨ T2 <: T ] ->
    [ Θ; Γ ⊨ T_union T1 T2 <: T ].
Proof.
  unfold open_subtype; repeat step; eauto using subtype_union_left.
Qed.

Opaque List.

Lemma open_submatch_helper:
  forall Θ Γ t1 T2 T3 S x y,
    x <> y ->
    ~x ∈ fv S ->
    ~x ∈ fv t1 ->
    ~x ∈ fv T3 ->
    ~x ∈ pfv_context Γ term_var ->
    ~y ∈ fv S ->
    ~y ∈ fv t1 ->
    ~y ∈ fv T3 ->
    ~y ∈ pfv_context Γ term_var ->
    wf t1 0 ->
    [ Θ; Γ ⊨ t1 : List ] ->
    [ Θ; Γ ⊨ T2 <: S ] ->
    [ Θ; (y, List) :: (x, T_top) :: Γ ⊨ open 0 (open 1 T3 (fvar x term_var)) (fvar y term_var) <: S ] ->
    [ Θ; Γ ⊨ List_Match t1 T2 T3 <: S ].
Proof.
  unfold List_Match; intros; apply open_subtype_union_left; steps.
  - unfold open_subtype, subtype; repeat step || simp_red_top_level_hyp.
    unfold open_subtype in H2; eauto using subtype_reducible_values.

  - apply open_sub_exists_left_helper with x; repeat step || list_utils.
    apply open_sub_exists_left_helper with y;
      repeat step || list_utils || fv_open || open_none.
    rewrite (open_none t1) by eauto with wf.
    unfold open_subtype, subtype in H11.
    unfold open_subtype, subtype; repeat step || simp_red_top_level_hyp.
Qed.

Lemma open_submatch:
  forall Γ t1 T2 T3 S x y,
    x <> y ->
    ~x ∈ fv S ->
    ~x ∈ fv t1 ->
    ~x ∈ fv T3 ->
    ~x ∈ pfv_context Γ term_var ->
    ~y ∈ fv S ->
    ~y ∈ fv t1 ->
    ~y ∈ fv T3 ->
    ~y ∈ pfv_context Γ term_var ->
    wf t1 0 ->
    [ Γ ⊨ t1 : List ] ->
    [ Γ ⊨ T2 <: S ] ->
    [ (y, List) :: (x, T_top) :: Γ ⊨ open 0 (open 1 T3 (fvar x term_var)) (fvar y term_var) <: S ] ->
    [ Γ ⊨ List_Match t1 T2 T3 <: S ].
Proof.
  eauto using open_submatch_helper.
Qed.
