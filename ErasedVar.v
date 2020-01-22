Require Import Equations.Equations.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Require Export SystemFR.RedTactics.

Opaque reducible_values.
Opaque makeFresh.

Lemma open_reducible_weaken:
  forall theta (gamma : context) (x : nat) T u U,
    open_reducible theta gamma u U ->
    ~(x ∈ support gamma) ->
    ~(x ∈ fv u) ->
    ~(x ∈ fv U) ->
    open_reducible theta ((x, T) :: gamma) u U.
Proof.
    unfold open_reducible in *; repeat step || step_inversion satisfies || tac1.
Qed.

Lemma open_reducible_var:
  forall tvars gamma x T,
    lookup Nat.eq_dec gamma x = Some T ->
    open_reducible tvars gamma (term_fvar x) T.
Proof.
  unfold open_reducible;
    repeat step || t_termlist || t_lookup;
    eauto using reducible_value_expr.
Qed.
