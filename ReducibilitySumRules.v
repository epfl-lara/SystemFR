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
Require Import SystemFR.ErasedTermLemmas.
Require Import SystemFR.StarRelation.

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

Lemma reducible_left:
  forall theta t A B,
    valid_interpretation theta ->
    reducible theta t A ->
    reducible theta (tleft t) (T_sum A B).
Proof.
  unfold reducible, reduces_to; steps.
  eexists; steps; eauto with bsteplemmas;
    repeat step || simp_red || t_closing; eauto with values.
Qed.

Lemma open_reducible_left:
  forall tvars gamma t A B,
    open_reducible tvars gamma t A ->
    open_reducible tvars gamma (tleft t) (T_sum A B).
Proof.
  unfold open_reducible; steps; eauto using reducible_left.
Qed.

Lemma reducible_right:
  forall theta t A B,
    valid_interpretation theta ->
    reducible theta t B ->
    reducible theta (tright t) (T_sum A B).
Proof.
  unfold reducible, reduces_to; steps.
  eexists; steps; eauto with bsteplemmas;
    repeat step || simp_red || t_closing; eauto with values.
Qed.

Lemma open_reducible_right:
  forall tvars gamma t A B,
    open_reducible tvars gamma t B ->
    open_reducible tvars gamma (tright t) (T_sum A B).
Proof.
  unfold open_reducible; steps; eauto using reducible_right.
Qed.

Lemma open_reducible_sum_match:
  forall tvars (gamma : context) t tl tr T1 T2 T y p,
    subset (fv t) (support gamma) ->
    subset (fv tl) (support gamma) ->
    subset (fv tr) (support gamma) ->
    subset (fv T1) (support gamma) ->
    subset (fv T2) (support gamma) ->
    wf T1 0 ->
    wf T2 0 ->
    wf t 0 ->
    wf tr 1 ->
    wf tl 1 ->
    ~(y ∈ fv_context gamma) ->
    ~(y ∈ fv T) ->
    ~(y ∈ fv T1) ->
    ~(y ∈ fv T2) ->
    ~(y ∈ pfv T term_var) ->
    ~(p ∈ pfv_context gamma term_var) ->
    ~(p ∈ pfv t term_var) ->
    ~(p ∈ pfv T1 term_var) ->
    ~(p ∈ pfv T2 term_var) ->
    ~(p ∈ pfv T term_var) ->
    ~(p = y) ->
    is_erased_term t ->
    is_erased_term tl ->
    is_erased_term tr ->
    open_reducible tvars gamma t (T_sum T1 T2) ->
    open_reducible tvars
                   ((p, T_equal t (tleft (fvar y term_var))) :: (y, T1) :: gamma)
                   (open 0 tl (fvar y term_var))
                   (open 0 T (tleft (fvar y term_var))) ->
    open_reducible tvars
                   ((p, T_equal t (tright (fvar y term_var))) :: (y, T2) :: gamma)
                   (open 0 tr (fvar y term_var))
                   (open 0 T (tright (fvar y term_var))) ->
    open_reducible tvars gamma (sum_match t tl tr) (T_let t T).
Proof.
  unfold open_reducible; repeat step || t_instantiate_sat3 || top_level_unfold || simp_red.

  - eapply reducible_let_backstep_expr; eauto; t_closer.
    apply reducible_let with (T_sum (psubstitute T1 lterms term_var) (psubstitute T2 lterms term_var)); repeat step || simp_red; eauto.

    unshelve epose proof (H24 theta ((p, uu) :: (y,v') :: lterms) _ _ _);
      repeat tac1 || t_values_info2 || t_deterministic_star.

    eapply star_backstep_reducible; eauto with bsteplemmas;
      repeat step || t_listutils; t_closer.
    eapply backstep_reducible; eauto with smallstep;
      repeat step || t_listutils; t_closer.

  - eapply reducible_let_backstep_expr; eauto; t_closer.
    apply reducible_let with (T_sum (psubstitute T1 lterms term_var) (psubstitute T2 lterms term_var)); repeat step || simp_red; eauto.

    unshelve epose proof (H25 theta ((p, uu) :: (y,v') :: lterms) _ _ _);
      repeat tac1 || t_values_info2 || t_deterministic_star.

    eapply star_backstep_reducible; eauto with bsteplemmas;
      repeat step || t_listutils; t_closer.
    eapply backstep_reducible; eauto with smallstep;
      repeat step || t_listutils; t_closer.
Qed.
