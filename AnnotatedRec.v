Require Import Coq.Lists.List.

Require Export SystemFR.ErasedRec.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.Judgments.
Require Export SystemFR.NatCompareErase.

Lemma annotated_reducible_unfold_z:
  forall tvars gamma t n T0 Ts,
    wf T0 0 ->
    wf Ts 0 ->
    twf T0 0 ->
    twf Ts 1 ->
    [[ tvars; gamma ⊨ n ≡ zero ]] ->
    [[ tvars; gamma ⊨ t : T_rec n T0 Ts ]] ->
    [[ tvars; gamma ⊨ tunfold t : T0 ]].
Proof.
  unfold annotated_reducible, annotated_equivalent, equivalent;
    repeat step.

  apply open_reducible_unfold_zero with (erase_type Ts);
    steps;
    side_conditions.

  unfold open_reducible in *; repeat step || t_instantiate_sat3;
    eauto using reducible_rec_equivalent.
Qed.

Lemma annotated_reducible_unfold_s:
  forall tvars gamma t n T0 Ts,
    is_annotated_term n ->
    wf n 0 ->
    wf T0 0 ->
    wf Ts 0 ->
    twf T0 0 ->
    twf Ts 1 ->
    is_annotated_type T0 ->
    is_annotated_type Ts ->
    is_annotated_term n ->
    subset (fv n) (support gamma) ->
    subset (fv T0) (support gamma) ->
    subset (fv Ts) (support gamma) ->
    [[ tvars; gamma ⊨ spositive n ≡ ttrue ]] ->
    [[ tvars; gamma ⊨ t : T_rec n T0 Ts ]] ->
    [[ tvars; gamma ⊨ tunfold t : topen 0 Ts (T_rec (tpred n) T0 Ts) ]].
Proof.
  unfold annotated_reducible, annotated_equivalent, equivalent;
    repeat step || erase_open.

  apply open_reducible_unfold2;
    repeat step || unfold spositive;
    side_conditions.
Qed.

Lemma annotated_reducible_unfold_in:
  forall tvars gamma t1 t2 n T0 Ts p1 p2 y T,
    ~(p1 ∈ tvars) ->
    ~(p1 ∈ fv_context gamma) ->
    ~(p1 ∈ fv t1) ->
    ~(p1 ∈ fv t2) ->
    ~(p1 ∈ fv n) ->
    ~(p1 ∈ fv T0) ->
    ~(p1 ∈ fv Ts) ->
    ~(p1 ∈ fv T) ->
    ~(p2 ∈ tvars) ->
    ~(p2 ∈ fv_context gamma) ->
    ~(p2 ∈ fv t1) ->
    ~(p2 ∈ fv t2) ->
    ~(p2 ∈ fv n) ->
    ~(p2 ∈ fv T0) ->
    ~(p2 ∈ fv Ts) ->
    ~(p2 ∈ fv T) ->
    ~(y ∈ tvars) ->
    ~(y ∈ fv_context gamma) ->
    ~(y ∈ fv t1) ->
    ~(y ∈ fv t2) ->
    ~(y ∈ fv n) ->
    ~(y ∈ fv T0) ->
    ~(y ∈ fv Ts) ->
    ~(y ∈ fv T) ->
    NoDup (p1 :: p2 :: y :: nil) ->
    is_annotated_term n ->
    is_annotated_term t2 ->
    is_annotated_type T0 ->
    is_annotated_type Ts ->
    wf n 0 ->
    wf T0 0 ->
    wf Ts 0 ->
    twf T0 0 ->
    twf Ts 1 ->
    wf t1 0 ->
    wf (erase_term t2) 0 ->
    subset (fv t1) (support gamma) ->
    subset (fv t2) (support gamma) ->
    subset (fv n) (support gamma) ->
    subset (fv T0) (support gamma) ->
    subset (fv Ts) (support gamma) ->
    [[ tvars; gamma ⊨ t1 : T_rec n T0 Ts ]] ->
    [[ tvars; (p2, T_equiv n zero) ::
              (p1, T_equiv t1 (tfold (T_rec n T0 Ts) (fvar y term_var))) ::
              (y, T0) :: gamma ⊨
         open 0 t2 (fvar y term_var) : T ]] ->
    [[ tvars; (p1, T_equiv t1 (tfold (T_rec n T0 Ts) (fvar y term_var))) ::
              (y, topen 0 Ts (T_rec (tpred n) T0 Ts)) ::
              gamma ⊨
         open 0 t2 (fvar y term_var) : T ]] ->
    [[ tvars; gamma ⊨ tunfold_in t1 t2 : T ]].
Proof.
  unfold annotated_reducible, annotated_equivalent, equivalent;
    repeat step || erase_open.

  apply open_reducible_unfold_in with (erase_term n) (erase_type T0) (erase_type Ts) p1 p2 y;
    repeat step;
    side_conditions.
Qed.

Lemma annnotated_reducible_unfold_pos_in:
  forall tvars gamma t1 t2 n T0 Ts p1 y T,
    ~(p1 ∈ tvars) ->
    ~(p1 ∈ fv_context gamma) ->
    ~(p1 ∈ fv t1) ->
    ~(p1 ∈ fv t2) ->
    ~(p1 ∈ fv n) ->
    ~(p1 ∈ fv T0) ->
    ~(p1 ∈ fv Ts) ->
    ~(p1 ∈ fv T) ->
    ~(y ∈ tvars) ->
    ~(y ∈ fv_context gamma) ->
    ~(y ∈ fv t1) ->
    ~(y ∈ fv t2) ->
    ~(y ∈ fv n) ->
    ~(y ∈ fv T0) ->
    ~(y ∈ fv Ts) ->
    ~(y ∈ fv T) ->
    NoDup (p1 :: y :: nil) ->
    is_annotated_term n ->
    is_annotated_term t2 ->
    is_annotated_type T0 ->
    is_annotated_type Ts ->
    wf n 0 ->
    wf T0 0 ->
    wf Ts 0 ->
    twf T0 0 ->
    twf Ts 1 ->
    wf t1 0 ->
    wf (erase_term t2) 0 ->
    subset (fv t1) (support gamma) ->
    subset (fv t2) (support gamma) ->
    subset (fv n) (support gamma) ->
    subset (fv T0) (support gamma) ->
    subset (fv Ts) (support gamma) ->
    [[ tvars; gamma ⊨ t1 : T_rec n T0 Ts ]] ->
    [[ tvars; gamma ⊨ annotated_tlt zero n ≡ ttrue ]] ->
    [[ tvars; (p1, T_equiv t1 (tfold (T_rec n T0 Ts) (fvar y term_var))) ::
              (y, topen 0 Ts (T_rec (tpred n) T0 Ts)) ::
              gamma  ⊨
         open 0 t2 (fvar y term_var) : T ]] ->
    [[ tvars; gamma ⊨ tunfold_pos_in t1 t2 : T ]].
Proof.
  unfold annotated_reducible, annotated_equivalent, equivalent;
    repeat step || erase_open.

  apply open_reducible_unfold_pos_in with (erase_term n) (erase_type T0) (erase_type Ts) p1 y;
    repeat step;
    side_conditions.
Qed.

Lemma annnotated_reducible_fold:
  forall tvars gamma t n pn T0 Ts p,
    ~(p ∈ tvars) ->
    ~(p ∈ fv_context gamma) ->
    ~(p ∈ fv t) ->
    ~(p ∈ fv n) ->
    ~(p ∈ fv T0) ->
    ~(p ∈ fv Ts) ->
    ~(pn ∈ tvars) ->
    ~(pn ∈ fv_context gamma) ->
    ~(pn ∈ fv t) ->
    ~(pn ∈ fv n) ->
    ~(pn ∈ fv T0) ->
    ~(pn ∈ fv Ts) ->
    ~(p = pn) ->
    wf n 0 ->
    twf n 0 ->
    wf T0 0 ->
    twf T0 0 ->
    wf Ts 0 ->
    twf Ts 1 ->
    subset (fv n) (support gamma) ->
    subset (fv T0) (support gamma) ->
    subset (fv Ts) (support gamma) ->
    is_annotated_term n ->
    is_annotated_type T0 ->
    is_annotated_type Ts ->
    [[ tvars; gamma ⊨ n : T_nat ]] ->
    [[ tvars; (p, T_equiv n zero) :: gamma ⊨ t : T0 ]] ->
    [[ tvars; (p, T_equiv n (succ (fvar pn term_var))) :: (pn, T_nat) :: gamma ⊨ t : topen 0 Ts (T_rec (fvar pn term_var) T0 Ts) ]] ->
    [[ tvars; gamma ⊨ tfold (T_rec n T0 Ts) t : T_rec n T0 Ts ]].
Proof.
  unfold annotated_reducible, annotated_equivalent, equivalent;
    repeat step || erase_open.

  apply open_reducible_fold2 with p pn;
    repeat step;
    side_conditions.
Qed.
