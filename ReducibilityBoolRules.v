Require Import Equations.Equations.

Require Import Termination.Syntax.
Require Import Termination.Tactics.
Require Import Termination.SmallStep.
Require Import Termination.StarInversions.
Require Import Termination.WFLemmas.
Require Import Termination.StarRelation.
Require Import Termination.StarLemmas.
Require Import Termination.Equivalence.
Require Import Termination.EquivalenceLemmas.
Require Import Termination.ListUtils.
Require Import Termination.Sets.
Require Import Termination.AssocList.
Require Import Termination.Freshness.
Require Import Termination.TermList.
Require Import Termination.SubstitutionLemmas.

Require Import Termination.ReducibilityDefinition.
Require Import Termination.ReducibilityLemmas.
Require Import Termination.RedTactics.

Require Import Termination.WFLemmasTermList.
Require Import Termination.FVLemmasTermList.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducible_ttrue:
  reducible_values ttrue T_bool.
Proof.
  unfold open_reducible, reducible, reduces_to in *; steps.
Qed.

Lemma open_reducible_ttrue:
  forall gamma,
    open_reducible gamma ttrue T_bool.
Proof.
  unfold open_reducible, reducible, reduces_to in *; steps;
    eauto using reducible_ttrue with smallstep.
Qed.

Hint Resolve open_reducible_ttrue: breducible.

Lemma reducible_tfalse:
  reducible_values tfalse T_bool.
Proof.
  unfold open_reducible, reducible, reduces_to in *; steps.
Qed.

Lemma open_reducible_tfalse:
  forall gamma,
    open_reducible gamma tfalse T_bool.
Proof.
  unfold open_reducible, reducible, reduces_to in *; steps;
    eauto using reducible_tfalse with smallstep.
Qed.

Hint Resolve open_reducible_tfalse: breducible.


Lemma reducible_ite:
  forall T t1 t2 t3,
    wf t2 0 ->
    wf t3 0 ->
    fv t2 = nil ->
    fv t3 = nil ->
    reducible t1 T_bool ->
    (equivalent t1 ttrue -> reducible t2 T) ->
    (equivalent t1 tfalse -> reducible t3 T) ->
    reducible (ite t1 t2 t3) T.
Proof.
  intros T t1 t2 t3 WF2 WF3 FV2 FV3 H1 H2 H3.
  unfold reducible, reduces_to in H1; repeat step || simp reducible_values in *.
    
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

Hint Resolve reducible_ite: breducible.

Lemma open_reducible_ite:
  forall gamma T t1 t2 t3 x,
    wf t2 0 ->
    wf t3 0 ->
    subset (fv t2) (support gamma) ->
    subset (fv t3) (support gamma) ->
    ~(x ∈ fv t1) ->
    ~(x ∈ fv T) ->
    ~(x ∈ fv_context gamma) ->
    open_reducible gamma t1 T_bool ->
    open_reducible ((x, T_equal t1 ttrue) :: gamma) t2 T ->
    open_reducible ((x, T_equal t1 tfalse) :: gamma) t3 T ->
    open_reducible gamma (ite t1 t2 t3) T.
Proof.
  intros; unfold open_reducible; steps.

  unfold open_reducible in *; apply reducible_ite; steps;
    eauto with bwf;
    eauto with bfv.

  - unshelve epose proof (H7 ((x,trefl) :: l) _); tac1. 
  - unshelve epose proof (H8 ((x,trefl) :: l) _); tac1. 
Qed.

Hint Resolve open_reducible_ite: breducible.
