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

Require Import Termination.ReducibilityCandidate.
Require Import Termination.ReducibilityDefinition.
Require Import Termination.ReducibilityLemmas.
Require Import Termination.ReducibilityLetRules.
Require Import Termination.ReducibilityLetTermRules.
Require Import Termination.RedTactics.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducible_intersection:
  forall theta e T1 T2,
    valid_interpretation theta ->
    reducible theta e T1 ->
    reducible theta e T2 ->
    reducible theta e (T_intersection T1 T2).
Proof.
  unfold reducible, reduces_to;
    repeat step || simp_red || t_values_info2 || t_deterministic_star || eauto || eexists.
Qed.

Lemma reducible_union:
  forall theta e T1 T2,
    valid_interpretation theta ->
    (reducible theta e T1 \/ reducible theta e T2) ->
    reducible theta e (T_union T1 T2).
Proof.
  unfold reducible, reduces_to;
    repeat step || simp_red || t_values_info2 || t_deterministic_star || eauto || eexists.
Qed.

Lemma open_reducible_intersection:
  forall tvars gamma e T1 T2,
    open_reducible tvars gamma e T1 ->
    open_reducible tvars gamma e T2 ->
    open_reducible tvars gamma e (T_intersection T1 T2).
Proof.
  unfold open_reducible; repeat step || apply reducible_intersection.
Qed.

Lemma reducible_singleton:
  forall theta (t1 t2 : term) T,
    valid_interpretation theta ->
    equivalent t1 t2 ->
    reducible theta t1 T ->
    reducible theta t1 (T_singleton t2).
Proof.
  unfold reducible, reduces_to, equivalent; repeat step || eauto || eexists || simp_red;
    eauto with bwf bfv;
    eauto with values.
Qed.

Lemma open_reducible_singleton:
  forall tvars (gamma : context) (t1 t2 : term) T,
    open_reducible tvars gamma t1 T ->
    (forall (l : list (nat * term)) theta,
       valid_interpretation theta ->
       support theta = tvars ->
       satisfies (reducible_values theta) gamma l -> equivalent (substitute t1 l) (substitute t2 l)) ->
    open_reducible tvars gamma t1 (T_singleton t2).
Proof.
  unfold open_reducible; repeat step;
    eauto using reducible_singleton.
Qed.

Lemma open_reducible_union_elim:
  forall tvars (gamma : context) (t t' : term) T1 T2 T z,
    subset (fv t') (support gamma) ->
    subset (fv T1) (support gamma) ->
    subset (fv T2) (support gamma) ->
    wf t' 1 ->
    wf T1 0 ->
    wf T2 0 ->
    ~(z ∈ fv_context gamma) ->
    ~(z ∈ fv t') ->
    ~(z ∈ fv T) ->
    ~(z ∈ fv T1) ->
    ~(z ∈ fv T2) ->
    open_reducible tvars gamma t (T_union T1 T2) ->
    open_reducible tvars ((z, T1) :: gamma) (open 0 t' (term_fvar z)) T ->
    open_reducible tvars ((z, T2) :: gamma) (open 0 t' (term_fvar z)) T ->
    open_reducible tvars gamma (tlet t (T_union T1 T2) t') T.
Proof.
  unfold open_reducible; repeat step || t_instantiate_sat3 || top_level_unfold || simp_red.

  - unshelve epose proof (H11 theta ((z,t'0) :: lterms) _ _ _);
      repeat tac1 || t_values_info2 || t_deterministic_star || apply reducible_let_rule.

  - unshelve epose proof (H12 theta ((z,t'0) :: lterms) _ _ _);
      repeat tac1 || t_values_info2 || t_deterministic_star || apply reducible_let_rule.
Qed.
