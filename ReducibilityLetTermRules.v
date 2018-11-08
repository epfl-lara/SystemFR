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
Require Import Termination.SetLemmas.
Require Import Termination.SubstitutionErase.
Require Import Termination.TreeLists.
Require Import Termination.TermListReducible.

Require Import Termination.Equivalence.
Require Import Termination.EquivalenceLemmas.

Require Import Termination.WFLemmas.
Require Import Termination.WFLemmasLists.

Require Import Termination.FVLemmas.
Require Import Termination.FVLemmasLists.

Require Import Termination.ReducibilityCandidate.
Require Import Termination.ReducibilityDefinition.
Require Import Termination.ReducibilityLemmas.
Require Import Termination.RedTactics.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducible_value_let:
  forall theta v t A B,
    wf t 1 ->
    pfv t term_var = nil ->
    is_erased_term t ->
    valid_interpretation theta ->
    reducible_values theta v A ->
    reducible theta (open 0 t v) B ->
    reducible theta (notype_tlet v t) B.
Proof.
  steps.
  eapply backstep_reducible; eauto using red_is_val with smallstep;
    repeat step || t_listutils;
    eauto 2 with bfv;
    eauto 2 with bwf;
    eauto with berased.
Qed.

Lemma reducible_let_rule:
  forall theta t1 t2 A B,
    wf t2 1 ->
    fv t2 = nil ->
    valid_interpretation theta ->
    reducible theta t1 A ->
    is_erased_term t2 ->
    (forall v,
        is_value v ->
        star small_step t1 v ->
        reducible theta (open 0 t2 v) B) ->
    reducible theta (notype_tlet t1 t2) B.
Proof.
  unfold reducible, reduces_to; repeat step || t_listutils; eauto with bfv.
  createHypothesis;
    repeat step || t_values_info2.
  eexists; steps; eauto.
  eapply star_smallstep_trans; eauto.
  eapply star_smallstep_trans; eauto with bsteplemmas;
    eauto using red_is_val with smallstep.
Qed.

Lemma open_reducible_let:
  forall tvars gamma t1 t2 A B x p,
    ~(p ∈ fv_context gamma) ->
    ~(p ∈ fv A) ->
    ~(p ∈ fv B) ->
    ~(p ∈ fv t1) ->
    ~(p ∈ fv t2) ->
    ~(x ∈ fv_context gamma) ->
    ~(x ∈ fv A) ->
    ~(x ∈ fv B) ->
    ~(x ∈ fv t1) ->
    ~(x ∈ fv t2) ->
    ~(x = p) ->
    wf t2 1 ->
    is_erased_term t2 ->
    subset (fv A) (support gamma) ->
    subset (fv t2) (support gamma) ->
    open_reducible tvars gamma t1 A ->
    open_reducible tvars ((p, T_equal (fvar x term_var) t1) :: (x,A) :: gamma)
                   (open 0 t2 (fvar x term_var)) B ->
    open_reducible tvars gamma (notype_tlet t1 t2) B.
Proof.
  unfold open_reducible; steps.

  eapply reducible_let_rule;
   repeat step || top_level_unfold || t_values_info2 || t_deterministic_star || t_termlist || t_instantiate_sat4;
      eauto with bwf; eauto using subset_same with bfv;
        eauto with berased.
  - unshelve epose proof (H15 theta ((p,trefl) :: (x,t') :: lterms) _ _); tac1;
      eauto 3 using equivalent_sym with b_equiv;
      eauto with berased.
Qed.
