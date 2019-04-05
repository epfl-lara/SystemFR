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
Require Import SystemFR.ReducibilityLetRules.
Require Import SystemFR.ReducibilityLetTermRules.
Require Import SystemFR.RedTactics.

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
    repeat step || simp_red || t_values_info2 || t_deterministic_star || eauto || eexists; t_closer.
Qed.

Lemma reducible_union:
  forall theta e T1 T2,
    valid_interpretation theta ->
    (reducible theta e T1 \/ reducible theta e T2) ->
    reducible theta e (T_union T1 T2).
Proof.
  unfold reducible, reduces_to;
    repeat step || simp_red || t_values_info2 || t_deterministic_star || eauto || eexists; t_closer.
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
  forall theta t1 t2 T,
    valid_interpretation theta ->
    is_erased_term t2 ->
    equivalent t1 t2 ->
    reducible theta t1 T ->
    reducible theta t1 (T_singleton t2).
Proof.
  unfold reducible, reduces_to, equivalent; repeat step || eauto || eexists || simp_red;
    eauto with bwf bfv;
    eauto with values;
    eauto with berased.
Qed.

Lemma open_reducible_singleton:
  forall tvars (gamma : context) t1 t2 T,
    open_reducible tvars gamma t1 T ->
    is_erased_term t2 ->
    (forall l theta,
       valid_interpretation theta ->
       support theta = tvars ->
       satisfies (reducible_values theta) gamma l -> equivalent (substitute t1 l) (substitute t2 l)) ->
    open_reducible tvars gamma t1 (T_singleton t2).
Proof.
  unfold open_reducible; repeat step.
  eapply reducible_singleton; eauto with berased.
Qed.

Lemma open_reducible_union_elim:
  forall tvars (gamma : context) t t' T1 T2 T z,
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
    is_erased_term t' ->
    open_reducible tvars gamma t (T_union T1 T2) ->
    open_reducible tvars ((z, T1) :: gamma) (open 0 t' (term_fvar z)) T ->
    open_reducible tvars ((z, T2) :: gamma) (open 0 t' (term_fvar z)) T ->
    open_reducible tvars gamma (notype_tlet t t') T.
Proof.
  unfold open_reducible; repeat step || t_instantiate_sat3 || top_level_unfold || simp_red.

  - unshelve epose proof (H12 theta ((z,t'0) :: lterms) _ _ _);
      repeat tac1 || t_values_info2 || t_deterministic_star ||
             apply reducible_let_rule with (psubstitute (T_union T1 T2) lterms term_var);
      eauto with berased.
  - unshelve epose proof (H13 theta ((z,t'0) :: lterms) _ _ _);
      repeat tac1 || t_values_info2 || t_deterministic_star ||
             apply reducible_let_rule with (psubstitute (T_union T1 T2) lterms term_var);
      eauto with berased.
Qed.
