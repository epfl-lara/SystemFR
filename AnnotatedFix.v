Require Import Coq.Lists.List.

Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.ErasedFix.
Require Export SystemFR.NatLessThanErase.

Opaque reducible_values.

Lemma annotated_reducible_fix_strong_induction:
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
    cbv_value (erase_term ts) ->
    [[ tvars;
        (p, T_equiv (fvar y term_var) (tfix T ts)) ::
        (y, T_forall (T_refine T_nat (annotated_tlt (lvar 0 term_var) (fvar n term_var))) T) ::
        (n, T_nat) ::
        gamma ⊨
        open 0 (open 1 ts (fvar n term_var)) (fvar y term_var) :
        open 0 T (fvar n term_var) ]]
    ->
    [[ tvars; gamma ⊨ tfix T ts : T_forall T_nat T ]].
Proof.
  unfold annotated_reducible; steps.
  apply open_reducible_fix_strong_induction with n y p;
    repeat step || erase_open ||
           (rewrite (open_none (erase_term ts)) in * by auto) ||
           (rewrite erase_type_shift in *);
    side_conditions.
Qed.
