Require Import Equations.Equations.

Require Import Coq.Lists.List.

Require Import Termination.Syntax.
Require Import Termination.Tactics.
Require Import Termination.ListUtils.
Require Import Termination.StarRelation.
Require Import Termination.SmallStep.
Require Import Termination.StarLemmas.
Require Import Termination.Sets.
Require Import Termination.AssocList.
Require Import Termination.StarInversions.
Require Import Termination.TermList.
Require Import Termination.Freshness.
Require Import Termination.TermList.
Require Import Termination.SubstitutionLemmas.

Require Import Termination.Equivalence.
Require Import Termination.EquivalenceLemmas.

Require Import Termination.WFLemmas.
Require Import Termination.WFLemmasTermList.

Require Import Termination.FVLemmas.
Require Import Termination.FVLemmasTermList.

Require Import Termination.ReducibilityDefinition.
Require Import Termination.ReducibilityLemmas.
Require Import Termination.RedTactics.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducible_value_let:
  forall v t A B,
    wf t 1 ->
    fv t = nil ->
    wf A 0 ->
    fv A = nil ->
    reducible_values v A ->
    reducible (open 0 t v) B ->
    reducible (tlet v A t) B.
Proof.
  steps.
  eapply backstep_reducible; eauto using red_is_val with smallstep;
    repeat step || t_listutils;
    eauto 2 with bfv;
    eauto 2 with bwf.
Qed.

Lemma reducible_let_rule:
  forall t1 t2 A B,
    wf t2 1 ->
    fv t2 = nil ->
    wf A 0 ->
    fv A = nil ->
    reducible t1 A ->
    (forall v,
        is_value v ->
        star small_step t1 v ->
        reducible (open 0 t2 v) B) ->
    reducible (tlet t1 A t2) B.
Proof.  
  unfold reducible, reduces_to; repeat step || t_listutils.
  createHypothesis;
    repeat step || t_values_info2.
  eexists; steps; eauto.
  eapply star_smallstep_trans; eauto.
  eapply star_smallstep_trans; eauto with bsteplemmas;
    eauto using red_is_val with smallstep.
Qed.

Lemma open_reducible_let:
  forall gamma t1 t2 A B x p,
    ~(p ∈ fv_context gamma) ->
    ~(p ∈ fv A) ->
    ~(p ∈ fv B) ->
    ~(p ∈ fv t1) ->
    ~(p ∈ fv t2) ->
    ~(x ∈ fv_context gamma) ->
    ~(x ∈ fv A) ->
    ~(x ∈ fv B) ->
    ~(x ∈ fv t1) ->
    ~(x ∈ fv t2) ->    ~(x = p) ->
    wf A 0 ->
    wf t2 1 ->
    subset (fv A) (support gamma) ->
    subset (fv t2) (support gamma) ->
    open_reducible gamma t1 A ->
    open_reducible ((p, T_equal (fvar x) t1) :: (x,A) :: gamma) (open 0 t2 (fvar x)) B ->
    open_reducible gamma (tlet t1 A t2) B.
Proof.
  unfold open_reducible; steps.

  eapply reducible_let_rule;
   repeat step || tt || top_level_unfold || t_values_info2 || t_deterministic_star;
      eauto with bwf; eauto with bfv.
    unshelve epose proof (H15 ((p,trefl) :: (x,t') :: l) _); tac1;
      eauto 3 using equivalent_sym with b_equiv.
Qed.
