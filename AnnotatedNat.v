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
      (p, T_equiv tn (succ (fvar n term_var))) ::
      (n, T_nat) ::
      gamma
    ) ⊨
      open 0 ts (fvar n term_var) :
      T
    ]]
    ->
    [[ tvars; gamma ⊨ tmatch tn t0 ts : T ]].
Proof.
  unfold annotated_reducible; repeat step || erase_open.
  apply open_reducible_match with n p; repeat step || erase_open; side_conditions.
Qed.
