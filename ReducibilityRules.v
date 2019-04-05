Require Import Equations.Equations.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Require Import SystemFR.Syntax.
Require Import SystemFR.Tactics.
Require Import SystemFR.TermProperties.
Require Import SystemFR.Sets.
Require Import SystemFR.TermList.
Require Import SystemFR.ListUtils.
Require Import SystemFR.AssocList.
Require Import SystemFR.Freshness.
Require Import SystemFR.SmallStep.
Require Import SystemFR.SubstitutionLemmas.
Require Import SystemFR.StarLemmas.
Require Import SystemFR.StarInversions.
Require Import SystemFR.SmallStepSubstitutions.
Require Import SystemFR.SubstitutionErase.
Require Import SystemFR.TreeLists.
Require Import SystemFR.TermListReducible.

Require Import SystemFR.Equivalence.
Require Import SystemFR.EquivalenceLemmas.

Require Import SystemFR.FVLemmas.
Require Import SystemFR.FVLemmasLists.


Require Import SystemFR.WFLemmas.
Require Import SystemFR.WFLemmasLists.

Require Import SystemFR.ReducibilityCandidate.
Require Import SystemFR.ReducibilityDefinition.
Require Import SystemFR.ReducibilityLemmas.
Require Import SystemFR.RedTactics.

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

Lemma reducible_satisfies_weaker:
  forall theta gamma1 gamma2 x T T' l,
    (forall t l,
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
    open_reducible tvars gamma (term_fvar x) T.
Proof.
  unfold open_reducible;
    repeat step || t_termlist || t_lookup;
    eauto using reducible_value_expr.
Qed.

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
  unfold reducible, reduces_to, equivalent; repeat step;
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
    eauto with bwf bfv berased.
Qed.

Lemma open_reducible_refl:
  forall tvars (gamma : context) t1 t2,
    is_erased_term t1 ->
    is_erased_term t2 ->
    (forall l theta,
      valid_interpretation theta ->
      support theta = tvars ->
      satisfies (reducible_values theta) gamma l ->
      equivalent (substitute t1 l) (substitute t2 l)) ->
    open_reducible tvars gamma notype_trefl (T_equal t1 t2).
Proof.
  unfold open_reducible, reducible, reduces_to;
    repeat step || t_termlist || simp_red || eexists;
    eauto with smallstep;
    eauto using equivalence_def;
    eauto using equivalence_def2;
    eauto with berased.
Qed.
