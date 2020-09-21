Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.ErasedRecGen.
Require Export SystemFR.StrictPositivityErased.
Require Export SystemFR.BaseTypeErase.

Opaque reducible_values.

Lemma annotated_reducible_unfold_gen:
  forall Θ Γ t T0 Ts X,
    wf T0 0 ->
    wf Ts 0 ->
    twf T0 0 ->
    twf Ts 1 ->
    is_annotated_type Ts ->
    is_annotated_type T0 ->
    subset (fv T0) (support Γ) ->
    subset (fv Ts) (support Γ) ->
    ~(X ∈ pfv Ts type_var) ->
    strictly_positive (topen 0 Ts (fvar X type_var)) (X :: nil) ->
    [[ Θ; Γ ⊨ t : intersect T0 Ts ]] ->
    [[ Θ; Γ ⊨ tunfold t : topen 0 Ts (intersect T0 Ts) ]].
Proof.
  repeat step || erase_open.

  apply open_reducible_unfold_gen with X;
    repeat step;
    side_conditions.

  change (fvar X type_var) with (erase_type (fvar X type_var)).
  rewrite <- erase_type_topen; repeat step || apply strictly_positive_erased;
    eauto 2 with annot.
Qed.

Lemma annotated_reducible_unfold_gen_in:
  forall Θ Γ t1 t2 T0 Ts p y T X,
    ~(p ∈ Θ) ->
    ~(p ∈ fv_context Γ) ->
    ~(p ∈ fv t1) ->
    ~(p ∈ fv t2) ->
    ~(p ∈ fv T0) ->
    ~(p ∈ fv Ts) ->
    ~(p ∈ fv T) ->
    ~(y ∈ Θ) ->
    ~(y ∈ fv_context Γ) ->
    ~(y ∈ fv t1) ->
    ~(y ∈ fv t2) ->
    ~(y ∈ fv T0) ->
    ~(y ∈ fv Ts) ->
    ~(y ∈ fv T) ->
    ~(X ∈ pfv Ts type_var) ->
    strictly_positive (topen 0 Ts (fvar X type_var)) (X :: nil) ->
    is_annotated_type T0 ->
    is_annotated_type Ts ->
    is_annotated_term t2 ->
    ~(p = y) ->
    wf T0 0 ->
    wf Ts 0 ->
    twf T0 0 ->
    twf Ts 1 ->
    wf t2 0 ->
    wf t1 0 ->
    subset (fv t1) (support Γ) ->
    subset (fv t2) (support Γ) ->
    subset (fv T0) (support Γ) ->
    subset (fv Ts) (support Γ) ->
    [[ Θ; Γ ⊨ t1 : intersect T0 Ts ]] ->
    [[ Θ; (p, T_equiv t1 (tfold  (intersect T0 Ts) (fvar y term_var))) ::
             (y, topen 0 Ts (intersect T0 Ts)) ::
             Γ ⊨
             open 0 t2 (fvar y term_var) : T ]] ->
    [[ Θ; Γ ⊨ tunfold_in t1 t2 : T ]].
Proof.
  intros; apply open_reducible_unfold_in_gen with (erase_type T0) (erase_type Ts) X p y;
    repeat step || erase_open;
    side_conditions.

  change (fvar X type_var) with (erase_type (fvar X type_var)).
  rewrite <- erase_type_topen; repeat step || apply strictly_positive_erased;
    eauto 2 with annot.
Qed.

Lemma annotated_reducible_fold_gen:
  forall Θ Γ t T0 Ts X,
    wf T0 0 ->
    twf T0 0 ->
    wf Ts 0 ->
    twf Ts 1 ->
    subset (fv T0) (support Γ) ->
    subset (fv Ts) (support Γ) ->
    is_annotated_type T0 ->
    is_annotated_type Ts ->
    ~(X ∈ pfv Ts type_var) ->
    [[ Θ; Γ ⊨ topen 0 Ts (T_rec zero T0 Ts) <: T0 ]] ->
    strictly_positive (topen 0 Ts (fvar X type_var)) (X :: nil) ->
    [[ Θ; Γ ⊨ t : topen 0 Ts (intersect T0 Ts) ]] ->
    [[ Θ; Γ ⊨ tfold (intersect T0 Ts) t : intersect T0 Ts ]].
Proof.
  unfold open_subtype; repeat step.

  apply open_reducible_fold_gen with X;
    repeat step || erase_open; side_conditions.

  - change (fvar X type_var) with (erase_type (fvar X type_var)).
    rewrite <- erase_type_topen; repeat step || apply strictly_positive_erased;
      eauto 2 with annot.

  - apply_any; repeat step || erase_open || t_substitutions.
Qed.

Lemma annotated_reducible_fold_gen2:
  forall Θ Γ t T0 Ts X,
    wf T0 0 ->
    twf T0 0 ->
    wf Ts 0 ->
    twf Ts 1 ->
    subset (fv T0) (support Γ) ->
    subset (fv Ts) (support Γ) ->
    base_type X (topen 0 Ts (fvar X type_var)) T0 ->
    is_annotated_type Ts ->
    ~(X ∈ pfv Ts type_var) ->
    strictly_positive (topen 0 Ts (fvar X type_var)) (X :: nil) ->
    [[ Θ; Γ ⊨ t : topen 0 Ts (intersect T0 Ts) ]] ->
    [[ Θ; Γ ⊨ tfold (intersect T0 Ts) t : intersect T0 Ts ]].
Proof.
  intros; apply open_reducible_fold_gen2 with X;
    repeat step || erase_open; side_conditions.

  - change (fvar X type_var) with (erase_type (fvar X type_var)).
    rewrite <- erase_type_topen; repeat step || apply strictly_positive_erased;
      eauto 2 with annot.
  - change (fvar X type_var) with (erase_type (fvar X type_var)).
    rewrite <- erase_type_topen; repeat step || apply base_type_erase.
Qed.
