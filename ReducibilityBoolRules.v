Require Import Equations.Equations.

Require Import Coq.Lists.List.

Require Import Termination.Syntax.
Require Import Termination.Tactics.
Require Import Termination.SmallStep.
Require Import Termination.StarInversions.
Require Import Termination.StarRelation.
Require Import Termination.StarLemmas.
Require Import Termination.Equivalence.
Require Import Termination.EquivalenceLemmas.
Require Import Termination.ListUtils.
Require Import Termination.AssocList.
Require Import Termination.Freshness.
Require Import Termination.TermList.
Require Import Termination.TypeList.
Require Import Termination.SubstitutionLemmas.
Require Import Termination.TypeErasure.
Require Import Termination.SubstitutionErase.
Require Import Termination.TreeLists.
Require Import Termination.TermListReducible.

Require Import Termination.Sets.
Require Import Termination.SetLemmas.

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

Lemma reducible_ttrue:
  forall theta, reducible_values theta ttrue T_bool.
Proof.
  repeat step || simp_red.
Qed.

Lemma open_reducible_ttrue:
  forall theta gamma,
    open_reducible theta gamma ttrue T_bool.
Proof.
  unfold open_reducible, reducible, reduces_to, closed_term in *; steps;
    eauto using reducible_ttrue with smallstep.
Qed.

Lemma reducible_tfalse:
  forall theta, reducible_values theta tfalse T_bool.
Proof.
  repeat step || simp_red.
Qed.

Lemma open_reducible_tfalse:
  forall theta gamma,
    open_reducible theta gamma tfalse T_bool.
Proof.
  unfold open_reducible, reducible, reduces_to, closed_term in *; steps;
    eauto using reducible_tfalse with smallstep.
Qed.

Lemma reducible_ite:
  forall theta T t1 t2 t3,
    wf t2 0 ->
    wf t3 0 ->
    pfv t2 term_var = nil ->
    pfv t3 term_var = nil ->
    is_erased_term t2 ->
    is_erased_term t3 ->
    valid_interpretation theta ->
    reducible theta t1 T_bool ->
    (equivalent t1 ttrue -> reducible theta t2 T) ->
    (equivalent t1 tfalse -> reducible theta t3 T) ->
    reducible theta (ite t1 t2 t3) T.
Proof.
  intros theta T t1 t2 t3 WF2 WF3 FV2 FV3 H0 H1 H2 H3.
  match goal with
  | H: reducible _ _ T_bool |- _ =>
    unfold reducible, reduces_to, closed_term in H
  end; repeat step || simp reducible_values in *.

  - apply star_backstep_reducible with (ite ttrue t2 t3); repeat step || t_listutils;
      auto with bsteplemmas; eauto with bfv; eauto with bwf.
    eapply backstep_reducible; repeat step || t_listutils;
      eauto 2 with smallstep;
      eauto with bfv;
      eauto with bwf;
      eauto with b_equiv.
  - apply star_backstep_reducible with (ite tfalse t2 t3); repeat step || t_listutils;
      auto with bsteplemmas; eauto with bfv; eauto with bwf.
    eapply backstep_reducible; repeat step || t_listutils;
      eauto 2 with smallstep;
      eauto with bfv;
      eauto with bwf;
      eauto with b_equiv.
Qed.

Lemma open_reducible_ite:
  forall tvars gamma T t1 t2 t3 x,
    wf t2 0 ->
    wf t3 0 ->
    subset (fv t2) (support gamma) ->
    subset (fv t3) (support gamma) ->
    ~(x ∈ fv t1) ->
    ~(x ∈ fv T) ->
    ~(x ∈ fv_context gamma) ->
    ~(x ∈ tvars) ->
    is_erased_term t1 ->
    is_erased_term t2 ->
    is_erased_term t3 ->
    open_reducible tvars gamma t1 T_bool ->
    open_reducible tvars ((x, T_equal t1 ttrue) :: gamma) t2 T ->
    open_reducible tvars ((x, T_equal t1 tfalse) :: gamma) t3 T ->
    open_reducible tvars gamma (ite t1 t2 t3) T.
Proof.
  intros; unfold open_reducible; steps.

  unfold open_reducible in *; apply reducible_ite; repeat step || t_termlist;
    eauto with bwf;
    eauto using subset_same with bfv;
    eauto with berased.

  - unshelve epose proof (H11 _ ((x,trefl) :: lterms) _ _ _); tac1.
  - unshelve epose proof (H12 _ ((x,trefl) :: lterms) _ _ _); tac1.
Qed.
