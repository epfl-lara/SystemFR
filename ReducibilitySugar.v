Require Import SystemFR.ReducibilityDefinition.
Require Import SystemFR.ReducibilityLemmas.
Require Import SystemFR.ReducibilityRefineRules.
Require Import SystemFR.ReducibilityTypeRefineRules.
Require Import SystemFR.ReducibilityLetRules.
Require Import SystemFR.ReducibilitySetOpsRules.
Require Import SystemFR.ReducibilityCandidate.

Require Import SystemFR.RedTactics.
Require Import SystemFR.RedTactics2.

Require Import SystemFR.Trees.
Require Import SystemFR.TypeSugar.
Require Import SystemFR.Sets.
Require Import SystemFR.Syntax.
Require Import SystemFR.AssocList.
Require Import SystemFR.Tactics.
Require Import SystemFR.TermList.
Require Import SystemFR.SmallStep.
Require Import SystemFR.StarRelation.
Require Import SystemFR.Equivalence.
Require Import SystemFR.ListUtils.

Require Import SystemFR.WFLemmas.

Require Import Coq.Lists.List.

Lemma open_reducible_T_ite:
  forall tvars gamma T1 T2 b t1 t2 x,
    wf t1 0 ->
    wf t2 0 ->
    wf T1 0 ->
    wf T2 0 ->
    is_erased_term t1 ->
    is_erased_term t2 ->
    is_erased_type T1 ->
    is_erased_type T2 ->
    subset (fv t1) (support gamma) ->
    subset (fv t2) (support gamma) ->
    subset (fv T1) (support gamma) ->
    subset (fv T2) (support gamma) ->
    ~(x ∈ fv b) ->
    ~(x ∈ fv t1) ->
    ~(x ∈ fv t2) ->
    ~(x ∈ fv T1) ->
    ~(x ∈ fv T2) ->
    ~(x ∈ fv_context gamma) ->
    ~(x ∈ tvars) ->
    is_erased_term b ->
    is_erased_term t1 ->
    is_erased_term t2 ->
    open_reducible tvars gamma b T_bool ->
    open_reducible tvars ((x, T_equal b ttrue) :: gamma) t1 T1 ->
    open_reducible tvars ((x, T_equal b tfalse) :: gamma) t2 T2 ->
    open_reducible tvars gamma (ite b t1 t2) (T_ite b T1 T2).
Proof.
  unfold open_reducible; repeat step || t_instantiate_sat3.
  repeat apply reducible_union || step || top_level_unfold || simp_red.

  - left.
    apply reducible_refine; repeat step || (rewrite open_none by eauto with bwf);
      eauto with bwf;
      eauto with berased;
      eauto with b_equiv.

    eapply star_backstep_reducible; repeat step || t_listutils; eauto with bsteplemmas;
      eauto with bfv;
      eauto with bwf;
      eauto with berased.

    eapply backstep_reducible; eauto with smallstep; repeat step || t_listutils;
      eauto with bfv bwf berased.

    unshelve epose proof (H22 theta ((x, uu) :: lterms) _ _); tac1.

  - right.
    apply reducible_refine; repeat step || (rewrite open_none by eauto with bwf);
      eauto with bwf;
      eauto with berased;
      eauto with b_equiv.

    eapply star_backstep_reducible; repeat step || t_listutils; eauto with bsteplemmas;
      eauto with bfv;
      eauto with bwf;
      eauto with berased.

    eapply backstep_reducible; eauto with smallstep; repeat step || t_listutils;
      eauto with bfv bwf berased.

    unshelve epose proof (H23 theta ((x, uu) :: lterms) _ _); tac1.
Qed.
