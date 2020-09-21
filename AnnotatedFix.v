Require Import Coq.Lists.List.

Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.ErasedFix.
Require Export SystemFR.NatLessThanErase.

Opaque reducible_values.

Lemma annotated_reducible_fix_strong_induction:
  forall Θ Γ ts T n y p,
    ~(n ∈ fv_context Γ) ->
    ~(y ∈ fv_context Γ) ->
    ~(p ∈ fv_context Γ) ->
    ~(n ∈ fv T) ->
    ~(n ∈ fv ts) ->
    ~(y ∈ fv T) ->
    ~(y ∈ fv ts) ->
    ~(p ∈ fv T) ->
    ~(p ∈ fv ts) ->
    ~(n ∈ Θ) ->
    ~(y ∈ Θ) ->
    ~(p ∈ Θ) ->
    NoDup (n :: y :: p :: nil) ->
    wf (erase_term ts) 1 ->
    wf T 1 ->
    subset (fv T) (support Γ) ->
    subset (fv ts) (support Γ) ->
    is_annotated_type T ->
    is_annotated_term ts ->
    cbv_value (erase_term ts) ->
    [[ Θ;
        (p, T_equiv (fvar y term_var) (tfix T ts)) ::
        (y, T_forall (T_refine T_nat (annotated_tlt (lvar 0 term_var) (fvar n term_var))) T) ::
        (n, T_nat) ::
        Γ ⊨
        open 0 (open 1 ts (fvar n term_var)) (fvar y term_var) :
        open 0 T (fvar n term_var) ]]
    ->
    [[ Θ; Γ ⊨ tfix T ts : T_forall T_nat T ]].
Proof.
  intros; apply open_reducible_fix_strong_induction with n y p;
    repeat step || erase_open ||
           (rewrite (open_none (erase_term ts)) in * by auto) ||
           (rewrite erase_type_shift in *);
    side_conditions.
Qed.
