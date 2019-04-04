Require Import Equations.Equations.

Require Import Coq.Lists.List.

Require Import SystemFR.Syntax.
Require Import SystemFR.Tactics.
Require Import SystemFR.SmallStep.
Require Import SystemFR.StarInversions.
Require Import SystemFR.StarRelation.
Require Import SystemFR.StarLemmas.
Require Import SystemFR.Equivalence.
Require Import SystemFR.EquivalenceLemmas.
Require Import SystemFR.ListUtils.
Require Import SystemFR.AssocList.
Require Import SystemFR.Freshness.
Require Import SystemFR.TermList.
Require Import SystemFR.SubstitutionLemmas.
Require Import SystemFR.SubstitutionErase.
Require Import SystemFR.TreeLists.
Require Import SystemFR.TermListReducible.

Require Import SystemFR.Sets.
Require Import SystemFR.SetLemmas.

Require Import SystemFR.WellFormed.
Require Import SystemFR.WFLemmas.
Require Import SystemFR.WFLemmasLists.

Require Import SystemFR.FVLemmas.
Require Import SystemFR.FVLemmasLists.

Require Import SystemFR.ReducibilityCandidate.
Require Import SystemFR.ReducibilityDefinition.
Require Import SystemFR.ReducibilityLemmas.
Require Import SystemFR.RedTactics.

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
  forall theta T b t1 t2,
    wf t1 0 ->
    wf t2 0 ->
    pfv t1 term_var = nil ->
    pfv t2 term_var = nil ->
    is_erased_term t1 ->
    is_erased_term t2 ->
    valid_interpretation theta ->
    reducible theta b T_bool ->
    (equivalent b ttrue -> reducible theta t1 T) ->
    (equivalent b tfalse -> reducible theta t2 T) ->
    reducible theta (ite b t1 t2) T.
Proof.
  intros.
  match goal with
  | H: reducible _ _ T_bool |- _ =>
    unfold reducible, reduces_to, closed_term in H
  end; repeat step || simp reducible_values in *.

  - apply star_backstep_reducible with (ite ttrue t1 t2); repeat step || t_listutils;
      auto with bsteplemmas; eauto with bfv; eauto with bwf.
    eapply backstep_reducible; repeat step || t_listutils;
      eauto 2 with smallstep;
      eauto with bfv;
      eauto with bwf;
      eauto with b_equiv.
  - apply star_backstep_reducible with (ite tfalse t1 t2); repeat step || t_listutils;
      auto with bsteplemmas; eauto with bfv; eauto with bwf.
    eapply backstep_reducible; repeat step || t_listutils;
      eauto 2 with smallstep;
      eauto with bfv;
      eauto with bwf;
      eauto with b_equiv.
Qed.

Lemma open_reducible_ite:
  forall tvars gamma T b t1 t2 x,
    wf t1 0 ->
    wf t2 0 ->
    subset (fv t1) (support gamma) ->
    subset (fv t2) (support gamma) ->
    ~(x ∈ fv b) ->
    ~(x ∈ fv T) ->
    ~(x ∈ fv_context gamma) ->
    ~(x ∈ tvars) ->
    is_erased_term b ->
    is_erased_term t1 ->
    is_erased_term t2 ->
    open_reducible tvars gamma b T_bool ->
    open_reducible tvars ((x, T_equal b ttrue) :: gamma) t1 T ->
    open_reducible tvars ((x, T_equal b tfalse) :: gamma) t2 T ->
    open_reducible tvars gamma (ite b t1 t2) T.
Proof.
  intros; unfold open_reducible; steps.

  unfold open_reducible in *; apply reducible_ite; repeat step || t_termlist;
    eauto with bwf;
    eauto using subset_same with bfv;
    eauto with berased.

  - unshelve epose proof (H11 _ ((x, notype_trefl) :: lterms) _ _ _); tac1.
  - unshelve epose proof (H12 _ ((x, notype_trefl) :: lterms) _ _ _); tac1.
Qed.
