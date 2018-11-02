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
Require Import Termination.FVLemmasTermList.

Require Import Termination.WFLemmas.
Require Import Termination.WFLemmasTermList.

Require Import Termination.ReducibilityDefinition.
Require Import Termination.ReducibilityLemmas.
Require Import Termination.ReducibilityLetRules.
Require Import Termination.ReducibilityLetTermRules.
Require Import Termination.RedTactics.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducible_intersection:
  forall e T1 T2,
    reducible e T1 ->
    reducible e T2 ->
    reducible e (T_intersection T1 T2).
Proof.
  unfold reducible, reduces_to;
    repeat step || simp_red || t_values_info2 || t_deterministic_star || eauto || eexists.
Qed.  

Lemma reducible_union:
  forall e T1 T2,
    (reducible e T1 \/ reducible e T2) ->
    reducible e (T_union T1 T2).
Proof.
  unfold reducible, reduces_to;
    repeat step || simp_red || t_values_info2 || t_deterministic_star || eauto || eexists.
Qed.  

Lemma open_reducible_intersection:
  forall gamma e T1 T2,
    open_reducible gamma e T1 ->
    open_reducible gamma e T2 ->
    open_reducible gamma e (T_intersection T1 T2).
Proof.
  unfold open_reducible; repeat step || apply reducible_intersection.
Qed.  

Lemma reducible_singleton:
  forall (t1 t2 : term) T,
    equivalent t1 t2 ->
    reducible t1 T ->
    reducible t1 (T_singleton t2).
Proof.
  unfold reducible, reduces_to, equivalent; repeat step || eauto || eexists;
    eauto with bwf bfv;
    eauto with values.
Qed.
  
Lemma open_reducible_singleton:
  forall (gamma : context) (t1 t2 : term) T,
    open_reducible gamma t1 T ->
    (forall l : list (nat * term),
        satisfies reducible_values gamma l -> equivalent (substitute t1 l) (substitute t2 l)) ->
    open_reducible gamma t1 (T_singleton t2).
Proof.
  unfold open_reducible; repeat step || tt;
    eauto using reducible_singleton.
Qed.
 
Lemma open_reducible_union_elim:
  forall (gamma : context) (t t' : term) T1 T2 T z,
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
    open_reducible gamma t (T_union T1 T2) ->
    open_reducible ((z, T1) :: gamma) (open 0 t' (fvar z)) T ->
    open_reducible ((z, T2) :: gamma) (open 0 t' (fvar z)) T ->
    open_reducible gamma (tlet t (T_union T1 T2) t') T.
Proof.
  unfold open_reducible; repeat step || tt || top_level_unfold || simp_red.

  - unshelve epose proof (H11 ((z,t'0) :: l) _);
      repeat tac1 || t_values_info2 || t_deterministic_star || apply reducible_let_rule.
    unfold reducible, reduces_to; repeat step || eauto || eexists || simp_red.

  - unshelve epose proof (H12 ((z,t'0) :: l) _);
      repeat tac1 || t_values_info2 || t_deterministic_star || apply reducible_let_rule.

    unfold reducible, reduces_to; repeat step || eauto || eexists || simp_red.
Qed.
