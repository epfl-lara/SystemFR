Require Import Equations.Equations.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Require Import Termination.Syntax.
Require Import Termination.Tactics.
Require Import Termination.TermProperties.
Require Import Termination.Sets.
Require Import Termination.TermList.
Require Import Termination.ListUtils.
Require Import Termination.AssocList.
Require Import Termination.Freshness.
Require Import Termination.SmallStep.
Require Import Termination.SubstitutionLemmas.
Require Import Termination.StarLemmas.
Require Import Termination.StarInversions.
Require Import Termination.SmallStepSubstitutions.

Require Import Termination.Equivalence.
Require Import Termination.EquivalenceLemmas.

Require Import Termination.FVLemmas.
Require Import Termination.FVLemmasLists.

Require Import Termination.WFLemmas.
Require Import Termination.WFLemmasLists.

Require Import Termination.ReducibilityDefinition.
Require Import Termination.ReducibilityLemmas.
Require Import Termination.ReducibilityLetRules.
Require Import Termination.ReducibilityLetTermRules.
Require Import Termination.RedTactics.

Opaque reducible_values.
Opaque makeFresh.

Lemma open_reducible_weaken:
  forall theta (gamma : context) (x : nat) T (u : term) U,
    open_reducible theta gamma u U ->
    ~(x ∈ support gamma) ->
    ~(x ∈ fv u) ->
    ~(x ∈ fv U) ->
    open_reducible theta ((x, T) :: gamma) u U.
Proof.
    unfold open_reducible in *; repeat step || step_inversion satisfies || tac1.
Qed.

Lemma reducible_satisfies_weaker:
  forall theta gamma1 gamma2 x T T' l,
    (forall (t : term) (l : list (nat * term)),
      satisfies (reducible_values theta) gamma2 l ->
      reducible_values theta t (substitute T l) ->
      reducible_values theta t (substitute T' l)) ->
    subset (fv T) (support gamma2) ->
    subset (fv T') (support gamma2) ->
    NoDup (support (gamma1 ++ (x, T) :: gamma2)) ->
    satisfies (reducible_values theta) (gamma1 ++ (x, T) :: gamma2) l ->
    satisfies (reducible_values theta) (gamma1 ++ (x, T') :: gamma2) l.
Proof.
  induction gamma1;
    repeat step || t_listutils || apply SatCons || step_inversion NoDup ||
           step_inversion satisfies.

  apply IHgamma1 with T; repeat step || t_listutils; eauto.
Qed.

Lemma open_reducible_var:
  forall tvars gamma x T,
    lookup Nat.eq_dec gamma x = Some T ->
    open_reducible tvars gamma (fvar x) T.
Proof.
  unfold open_reducible;
    repeat step || t_termlist || t_lookup;
    eauto using reducible_value_expr.
Qed.

Lemma reducible_equal:
  forall theta (t1 t2 : term) T,
    equivalent t1 t2 ->
    wf t2 0 ->
    fv t2 = nil ->
    valid_interpretation theta ->
    reducible theta t1 T ->
    reducible theta t2 T.
Proof.
  unfold reducible, reduces_to, equivalent; repeat step;
    eauto with values.
Qed.

Lemma open_reducible_equal:
  forall tvars (gamma : context) (t1 t2 : term) T,
    open_reducible tvars gamma t1 T ->
    (forall (l : list (nat * term)) theta,
      valid_interpretation theta ->
      support theta = tvars ->
      satisfies (reducible_values theta) gamma l ->
      equivalent (substitute t1 l) (substitute t2 l)) ->
    wf t2 0 ->
    subset (fv t2) (support gamma) ->
    open_reducible tvars gamma t2 T.
Proof.
  unfold open_reducible; repeat step || t_instantiate_sat3;
    eauto 6 using reducible_equal with bwf bfv.
Qed.

Lemma open_reducible_refl:
  forall tvars (gamma : context) (t1 t2 : term),
    (forall (l : list (nat * term)) theta,
      valid_interpretation theta ->
      support theta = tvars ->
      satisfies (reducible_values theta) gamma l ->
      equivalent (substitute t1 l) (substitute t2 l)) ->
    open_reducible tvars gamma trefl (T_equal t1 t2).
Proof.
  unfold open_reducible, reducible, reduces_to;
    repeat step || t_termlist || simp_red || eexists;
    eauto with smallstep;
    eauto using equivalence_def;
    eauto using equivalence_def2.
Qed.
