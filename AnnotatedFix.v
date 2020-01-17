Require Import Coq.Lists.List.

Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.ErasedFix.
Require Export SystemFR.NatCompareErase.
Require Export SystemFR.LVarOperationsErase.

Lemma annotated_reducible_fix:
  forall tvars gamma ts T n y p,
    ~(n ∈ fv_context gamma) ->
    ~(y ∈ fv_context gamma) ->
    ~(p ∈ fv_context gamma) ->
    ~(n ∈ fv T) ->
    ~(n ∈ fv ts) ->
    ~(y ∈ fv T) ->
    ~(y ∈ fv ts) ->
    ~(p ∈ fv T) ->
    ~(p ∈ fv ts) ->
    ~(n ∈ tvars) ->
    ~(y ∈ tvars) ->
    ~(p ∈ tvars) ->
    NoDup (n :: y :: p :: nil) ->
    wf (erase_term ts) 1 ->
    wf T 1 ->
    subset (fv T) (support gamma) ->
    subset (fv ts) (support gamma) ->
    is_annotated_type T ->
    is_annotated_term ts ->
    [[ tvars;
        (p, T_equiv (term_fvar y) (lambda T_unit (tfix T ts))) ::
        (y, T_arrow T_unit (open 0 T (term_fvar n))) ::
        (n, T_nat) ::
        gamma ⊨
          open 0 (open 1 ts (succ (fvar n term_var))) (term_fvar y) :
          open 0 T (succ (term_fvar n))
    ]] ->
    [[ tvars; (y, T_top) :: gamma ⊨
        open 0 (open 1 ts zero) (fvar y term_var) :
        open 0 T zero ]]
    ->
    [[ tvars; gamma ⊨ tfix T ts : T_forall T_nat T ]].
Proof.
  unfold annotated_reducible; steps.
  apply open_reducible_fix with n y p;
    repeat step || erase_open || rewrite (open_none (erase_term ts)) in * by auto;
    side_conditions.
Qed.

Lemma annotated_reducible_fix_strong_induct:
  forall tvars gamma ts T n y p,
    ~(n ∈ fv_context gamma) ->
    ~(y ∈ fv_context gamma) ->
    ~(p ∈ fv_context gamma) ->
    ~(n ∈ fv T) ->
    ~(n ∈ fv ts) ->
    ~(y ∈ fv T) ->
    ~(y ∈ fv ts) ->
    ~(p ∈ fv T) ->
    ~(p ∈ fv ts) ->
    ~(n ∈ tvars) ->
    ~(y ∈ tvars) ->
    ~(p ∈ tvars) ->
    NoDup (n :: y :: p :: nil) ->
    wf (erase_term ts) 1 ->
    wf T 1 ->
    subset (fv T) (support gamma) ->
    subset (fv ts) (support gamma) ->
    is_annotated_type T ->
    is_annotated_term ts ->
    [[ tvars;
        (p, T_equiv (term_fvar y) (lambda T_unit (tfix T ts))) ::
        (y,
          (T_forall
             (T_refine T_nat (annotated_tlt (lvar 0 term_var) (fvar n term_var)))
             (T_arrow T_unit (shift T)))) ::
        (n, T_nat) ::
        gamma ⊨
        open 0 (open 1 ts (fvar n term_var)) (term_fvar y) :
        open 0 T (term_fvar n) ]]
    ->
    [[ tvars; gamma ⊨ tfix T ts : T_forall T_nat T ]].
Proof.
  unfold annotated_reducible; steps.
  apply open_reducible_fix_strong_induction with n y p;
    repeat step || erase_open ||
           (rewrite (open_none (erase_term ts)) in * by auto) ||
           (rewrite erase_type_map_indices in *);
    side_conditions.
Qed.

