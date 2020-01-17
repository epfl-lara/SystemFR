Require Import Equations.Equations.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Require Export SystemFR.SubstitutionLemmas.
Require Export SystemFR.SmallStepSubstitutions.
Require Export SystemFR.SubstitutionErase.
Require Export SystemFR.TermListReducible.
Require Export SystemFR.LiftEquivalenceLemmas.
Require Export SystemFR.FVLemmasLists.
Require Export SystemFR.WFLemmasLists.
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

(*
Lemma reducible_equal:
  forall theta t1 t2 T,
    equivalent t1 t2 ->
    wf t2 0 ->
    pfv t2 term_var = nil ->
    pfv t2 type_var = nil ->
    is_erased_term t2 ->
    valid_interpretation theta ->
    reducible theta t1 T ->
    reducible theta t2 T.
Proof.
  unfold reducible, reduces_to; repeat step;
    eauto with values;
    try t_closer.
Qed.

Lemma open_reducible_equal:
  forall tvars gamma t1 t2 T,
    is_erased_term t2 ->
    open_reducible tvars gamma t1 T ->
    (forall l theta,
      valid_interpretation theta ->
      support theta = tvars ->
      satisfies (reducible_values theta) gamma l ->
      equivalent (substitute t1 l) (substitute t2 l)) ->
    wf t2 0 ->
    subset (fv t2) (support gamma) ->
    open_reducible tvars gamma t2 T.
Proof.
  unfold open_reducible;
    repeat tac1 || t_instantiate_sat3 ||
           apply reducible_equal with (psubstitute t1 lterms term_var);
    eauto with wf fv erased.
Qed.
*)
