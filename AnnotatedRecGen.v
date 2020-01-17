Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.ErasedRecGen.
Require Export SystemFR.StrictPositivityErased.
Require Export SystemFR.BaseTypeErase.

Lemma annotated_reducible_unfold_gen:
  forall tvars gamma t T0 Ts X,
    wf T0 0 ->
    wf Ts 0 ->
    twf T0 0 ->
    twf Ts 1 ->
    is_annotated_type Ts ->
    is_annotated_type T0 ->
    ~(X ∈ pfv Ts type_var) ->
    strictly_positive (topen 0 Ts (fvar X type_var)) (X :: nil) ->
    [[ tvars; gamma ⊨ t : intersect T0 Ts ]] ->
    [[ tvars; gamma ⊨ tunfold t : topen 0 Ts (intersect T0 Ts) ]].
Proof.
  unfold annotated_reducible;
    repeat step || erase_open.

  apply open_reducible_unfold_gen with X;
    repeat step;
    side_conditions.

  change (fvar X type_var) with (erase_type (fvar X type_var)).
  rewrite <- erase_type_topen; repeat step || apply strictly_positive_erased;
    eauto 2 with bannot.
Qed.

Lemma annotated_reducible_unfold_gen_in:
  forall tvars gamma t1 t2 T0 Ts p y T X,
    ~(p ∈ tvars) ->
    ~(p ∈ fv_context gamma) ->
    ~(p ∈ fv t1) ->
    ~(p ∈ fv t2) ->
    ~(p ∈ fv T0) ->
    ~(p ∈ fv Ts) ->
    ~(p ∈ fv T) ->
    ~(y ∈ tvars) ->
    ~(y ∈ fv_context gamma) ->
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
    subset (fv t1) (support gamma) ->
    subset (fv t2) (support gamma) ->
    [[ tvars; gamma ⊨ t1 : intersect T0 Ts ]] ->
    [[ tvars; (p, T_equiv t1 (tfold  (intersect T0 Ts) (fvar y term_var))) ::
             (y, topen 0 Ts (intersect T0 Ts)) ::
             gamma ⊨
             open 0 t2 (fvar y term_var) : T ]] ->
    [[ tvars; gamma ⊨ tunfold_in t1 t2 : T ]].
Proof.
  unfold annotated_reducible;
    repeat step.

  apply open_reducible_unfold_in_gen with (erase_type T0) (erase_type Ts) X p y;
    repeat step || erase_open;
    side_conditions.

  change (fvar X type_var) with (erase_type (fvar X type_var)).
  rewrite <- erase_type_topen; repeat step || apply strictly_positive_erased;
    eauto 2 with bannot.
Qed.


Lemma annotated_reducible_fold_gen:
  forall tvars gamma t T0 Ts X,
    wf T0 0 ->
    twf T0 0 ->
    wf Ts 0 ->
    twf Ts 1 ->
    subset (fv T0) (support gamma) ->
    subset (fv Ts) (support gamma) ->
    is_annotated_type T0 ->
    is_annotated_type Ts ->
    ~(X ∈ pfv Ts type_var) ->
    [[ tvars; gamma ⊨ topen 0 Ts (T_rec zero T0 Ts) <: T0 ]] ->
    strictly_positive (topen 0 Ts (fvar X type_var)) (X :: nil) ->
    [[ tvars; gamma ⊨ t : topen 0 Ts (intersect T0 Ts) ]] ->
    [[ tvars; gamma ⊨ tfold (intersect T0 Ts) t : intersect T0 Ts ]].
Proof.
  unfold annotated_reducible, annotated_subtype, subtype;
    repeat step.

  apply open_reducible_fold_gen with X;
    repeat step || erase_open; side_conditions.

  - change (fvar X type_var) with (erase_type (fvar X type_var)).
    rewrite <- erase_type_topen; repeat step || apply strictly_positive_erased;
      eauto 2 with bannot.

  - apply_any; repeat step || erase_open || t_substitutions.
Qed.

Lemma annotated_reducible_fold_gen2:
  forall tvars gamma t T0 Ts X,
    wf T0 0 ->
    twf T0 0 ->
    wf Ts 0 ->
    twf Ts 1 ->
    subset (fv Ts) (support gamma) ->
    base_type X (topen 0 Ts (fvar X type_var)) T0 ->
    is_annotated_type Ts ->
    ~(X ∈ pfv Ts type_var) ->
    strictly_positive (topen 0 Ts (fvar X type_var)) (X :: nil) ->
    [[ tvars; gamma ⊨ t : topen 0 Ts (intersect T0 Ts) ]] ->
    [[ tvars; gamma ⊨ tfold (intersect T0 Ts) t : intersect T0 Ts ]].
Proof.
  unfold annotated_reducible;
    repeat step.

  apply open_reducible_fold_gen2 with X;
    repeat step || erase_open; side_conditions.

  - change (fvar X type_var) with (erase_type (fvar X type_var)).
    rewrite <- erase_type_topen; repeat step || apply strictly_positive_erased;
      eauto 2 with bannot.
  - change (fvar X type_var) with (erase_type (fvar X type_var)).
    rewrite <- erase_type_topen; repeat step || apply base_type_erase.
Qed.
