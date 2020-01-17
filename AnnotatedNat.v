Require Import Coq.Lists.List.

Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.ErasedNat.

Lemma annotated_reducible_zero:
  forall tvars gamma,
    [[ tvars; gamma ⊨ zero : T_nat ]].
Proof.
  unfold annotated_reducible; eauto using open_reducible_zero.
Qed.

Lemma annotated_reducible_succ:
  forall tvars gamma t,
    [[ tvars; gamma ⊨ t : T_nat ]] ->
    [[ tvars; gamma ⊨ succ t : T_nat ]].
Proof.
  unfold annotated_reducible; eauto using open_reducible_succ.
Qed.

Lemma annotated_reducible_match:
  forall tvars gamma tn t0 ts T n p,
    ~(p ∈ fv ts) ->
    ~(p ∈ fv t0) ->
    ~(p ∈ fv tn) ->
    ~(p ∈ fv T) ->
    ~(p ∈ fv_context gamma) ->
    ~(n ∈ fv tn) ->
    ~(n ∈ fv ts) ->
    ~(n ∈ fv T) ->
    ~(n ∈ fv_context gamma) ->
    ~(n = p) ->
    ~(n ∈ tvars) ->
    ~(p ∈ tvars) ->
    wf ts 1 ->
    wf t0 0 ->
    subset (fv t0) (support gamma) ->
    subset (fv ts) (support gamma) ->
    is_annotated_term ts ->
    [[ tvars; gamma ⊨ tn : T_nat ]] ->
    [[ tvars; (p, T_equiv tn zero) :: gamma ⊨ t0 : T ]] ->
    [[ tvars; (
      (p, T_equiv tn (succ (term_fvar n))) ::
      (n, T_nat) ::
      gamma
    ) ⊨
      open 0 ts (term_fvar n) :
      T
    ]]
    ->
    [[ tvars; gamma ⊨ tmatch tn t0 ts : T ]].
Proof.
  unfold annotated_reducible; repeat step || erase_open.
  apply open_reducible_match with n p; repeat step || erase_open; side_conditions.
Qed.

Lemma annotated_reducible_rec:
  forall tvars gamma tn t0 ts T n y p,
    ~(n ∈ fv_context gamma) ->
    ~(y ∈ fv_context gamma) ->
    ~(p ∈ fv_context gamma) ->
    ~(n ∈ fv T) ->
    ~(n ∈ fv ts) ->
    ~(n ∈ fv t0) ->
    ~(n ∈ fv tn) ->
    ~(y ∈ fv T) ->
    ~(y ∈ fv ts) ->
    ~(y ∈ fv t0) ->
    ~(p ∈ fv T) ->
    ~(p ∈ fv ts) ->
    ~(p ∈ fv t0) ->
    ~(p ∈ fv tn) ->
    ~(n ∈ tvars) ->
    ~(y ∈ tvars) ->
    ~(p ∈ tvars) ->
    NoDup (n :: y :: p :: nil) ->
    is_annotated_type T ->
    is_annotated_term tn ->
    is_annotated_term ts ->
    subset (fv T) (support gamma) ->
    subset (fv t0) (support gamma) ->
    subset (fv ts) (support gamma) ->
    wf T 1 ->
    wf ts 2 ->
    [[ tvars; gamma ⊨ tn : T_nat ]] ->
    [[ tvars; gamma ⊨ t0 : open 0 T zero ]] ->
    [[ tvars;
        (p, T_equiv (term_fvar y) (lambda T_unit (rec T (term_fvar n) t0 ts))) ::
        (y, T_arrow T_unit (open 0 T (term_fvar n))) ::
        (n, T_nat) ::
        gamma ⊨

        open 0 (open 1 ts (term_fvar n)) (term_fvar y) :
        open 0 T (succ (term_fvar n))
    ]]
    ->
    [[ tvars; gamma ⊨ rec T tn t0 ts : open 0 T tn ]].
Proof.
  unfold annotated_reducible; repeat step || erase_open.
  apply open_reducible_rec with n y p;
    repeat step || erase_open; side_conditions.
Qed.
