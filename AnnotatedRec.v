Require Import Coq.Lists.List.

Require Export SystemFR.ErasedRec.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.Judgments.

Opaque reducible_values.

Lemma annotated_reducible_unfold_z:
  forall Θ Γ t n T0 Ts,
    wf T0 0 ->
    wf Ts 0 ->
    twf T0 0 ->
    twf Ts 1 ->
    [[ Θ; Γ ⊨ n ≡ zero ]] ->
    [[ Θ; Γ ⊨ t : T_rec n T0 Ts ]] ->
    [[ Θ; Γ ⊨ tunfold t : T0 ]].
Proof.
  unfold open_equivalent;
    repeat step.

  apply open_reducible_unfold_zero with (erase_type Ts);
    steps;
    side_conditions.

  unfold open_reducible in *; repeat step || t_instantiate_sat3;
    eauto using reducible_rec_equivalent.
Qed.

Lemma annotated_reducible_unfold_s:
  forall Θ Γ t n T0 Ts,
    is_annotated_term n ->
    wf n 0 ->
    wf T0 0 ->
    wf Ts 0 ->
    twf T0 0 ->
    twf Ts 1 ->
    is_annotated_type T0 ->
    is_annotated_type Ts ->
    is_annotated_term n ->
    subset (fv n) (support Γ) ->
    subset (fv T0) (support Γ) ->
    subset (fv Ts) (support Γ) ->
    [[ Θ; Γ ⊨ spositive n ≡ ttrue ]] ->
    [[ Θ; Γ ⊨ t : T_rec n T0 Ts ]] ->
    [[ Θ; Γ ⊨ tunfold t : topen 0 Ts (T_rec (tpred n) T0 Ts) ]].
Proof.
  unfold open_equivalent;
    repeat step || erase_open.

  apply open_reducible_unfold2;
    repeat step || unfold spositive;
    side_conditions.
Qed.

Lemma annotated_reducible_unfold_in:
  forall Θ Γ t1 t2 n T0 Ts p1 p2 y T,
    ~(p1 ∈ Θ) ->
    ~(p1 ∈ fv_context Γ) ->
    ~(p1 ∈ fv t1) ->
    ~(p1 ∈ fv t2) ->
    ~(p1 ∈ fv n) ->
    ~(p1 ∈ fv T0) ->
    ~(p1 ∈ fv Ts) ->
    ~(p1 ∈ fv T) ->
    ~(p2 ∈ Θ) ->
    ~(p2 ∈ fv_context Γ) ->
    ~(p2 ∈ fv t1) ->
    ~(p2 ∈ fv t2) ->
    ~(p2 ∈ fv n) ->
    ~(p2 ∈ fv T0) ->
    ~(p2 ∈ fv Ts) ->
    ~(p2 ∈ fv T) ->
    ~(y ∈ Θ) ->
    ~(y ∈ fv_context Γ) ->
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
    subset (fv t1) (support Γ) ->
    subset (fv t2) (support Γ) ->
    subset (fv n) (support Γ) ->
    subset (fv T0) (support Γ) ->
    subset (fv Ts) (support Γ) ->
    [[ Θ; Γ ⊨ t1 : T_rec n T0 Ts ]] ->
    [[ Θ; (p2, T_equiv n zero) ::
              (p1, T_equiv t1 (tfold (T_rec n T0 Ts) (fvar y term_var))) ::
              (y, T0) :: Γ ⊨
         open 0 t2 (fvar y term_var) : T ]] ->
    [[ Θ; (p1, T_equiv t1 (tfold (T_rec n T0 Ts) (fvar y term_var))) ::
              (y, topen 0 Ts (T_rec (tpred n) T0 Ts)) ::
              Γ ⊨
         open 0 t2 (fvar y term_var) : T ]] ->
    [[ Θ; Γ ⊨ tunfold_in t1 t2 : T ]].
Proof.
  unfold open_equivalent;
    repeat step || erase_open.

  apply open_reducible_unfold_in with (erase_term n) (erase_type T0) (erase_type Ts) p1 p2 y;
    repeat step;
    side_conditions.
Qed.

Lemma annnotated_reducible_unfold_pos_in:
  forall Θ Γ t1 t2 n T0 Ts p1 y T,
    ~(p1 ∈ Θ) ->
    ~(p1 ∈ fv_context Γ) ->
    ~(p1 ∈ fv t1) ->
    ~(p1 ∈ fv t2) ->
    ~(p1 ∈ fv n) ->
    ~(p1 ∈ fv T0) ->
    ~(p1 ∈ fv Ts) ->
    ~(p1 ∈ fv T) ->
    ~(y ∈ Θ) ->
    ~(y ∈ fv_context Γ) ->
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
    subset (fv t1) (support Γ) ->
    subset (fv t2) (support Γ) ->
    subset (fv n) (support Γ) ->
    subset (fv T0) (support Γ) ->
    subset (fv Ts) (support Γ) ->
    [[ Θ; Γ ⊨ t1 : T_rec n T0 Ts ]] ->
    [[ Θ; Γ ⊨ binary_primitive Lt zero n ≡ ttrue ]] ->
    [[ Θ; (p1, T_equiv t1 (tfold (T_rec n T0 Ts) (fvar y term_var))) ::
              (y, topen 0 Ts (T_rec (tpred n) T0 Ts)) ::
              Γ  ⊨
         open 0 t2 (fvar y term_var) : T ]] ->
    [[ Θ; Γ ⊨ tunfold_pos_in t1 t2 : T ]].
Proof.
  unfold open_equivalent;
    repeat step || erase_open.

  apply open_reducible_unfold_pos_in with (erase_term n) (erase_type T0) (erase_type Ts) p1 y;
    repeat step;
    side_conditions.
Qed.

Lemma annnotated_reducible_fold:
  forall Θ Γ t n pn T0 Ts p,
    ~(p ∈ Θ) ->
    ~(p ∈ fv_context Γ) ->
    ~(p ∈ fv t) ->
    ~(p ∈ fv n) ->
    ~(p ∈ fv T0) ->
    ~(p ∈ fv Ts) ->
    ~(pn ∈ Θ) ->
    ~(pn ∈ fv_context Γ) ->
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
    subset (fv n) (support Γ) ->
    subset (fv T0) (support Γ) ->
    subset (fv Ts) (support Γ) ->
    is_annotated_term n ->
    is_annotated_type T0 ->
    is_annotated_type Ts ->
    [[ Θ; Γ ⊨ n : T_nat ]] ->
    [[ Θ; (p, T_equiv n zero) :: Γ ⊨ t : T0 ]] ->
    [[ Θ; (p, T_equiv n (succ (fvar pn term_var))) :: (pn, T_nat) :: Γ ⊨ t : topen 0 Ts (T_rec (fvar pn term_var) T0 Ts) ]] ->
    [[ Θ; Γ ⊨ tfold (T_rec n T0 Ts) t : T_rec n T0 Ts ]].
Proof.
  unfold open_equivalent;
    repeat step || erase_open.

  apply open_reducible_fold2 with p pn;
    repeat step;
    side_conditions.
Qed.
