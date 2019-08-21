Require Import Omega.
Require Import Equations.Equations.

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import SystemFR.Sets.
Require Import SystemFR.Tactics.
Require Import SystemFR.Syntax.
Require Import SystemFR.TermList.
Require Import SystemFR.SmallStep.
Require Import SystemFR.AssocList.
Require Import SystemFR.EquivalenceLemmas.
Require Import SystemFR.ListUtils.
Require Import SystemFR.SubstitutionLemmas.
Require Import SystemFR.StarRelation.
Require Import SystemFR.SizeLemmas.
Require Import SystemFR.StarLemmas.
Require Import SystemFR.TypeErasure.
Require Import SystemFR.SubstitutionErase.
Require Import SystemFR.TreeLists.
Require Import SystemFR.TermListReducible.
Require Import SystemFR.StarInversions.
Require Import SystemFR.EquivalentWithRelation.
Require Import SystemFR.TermProperties.
Require Import SystemFR.ErasedTermLemmas.
Require Import SystemFR.SomeTerms.
Require Import SystemFR.TermListLemmas.

Require Import SystemFR.Equivalence.
Require Import SystemFR.EquivalenceLemmas.

Require Import SystemFR.EqualWithRelation.

Require Import SystemFR.ReducibilityCandidate.
Require Import SystemFR.ReducibilityDefinition.
Require Import SystemFR.ReducibilityLemmas.
Require Import SystemFR.ReducibilityRenaming.
Require Import SystemFR.ReducibilityUnused.
Require Import SystemFR.ReducibilitySubst.
Require Import SystemFR.ReducibilityRecRules.
Require Import SystemFR.RedTactics.

Require Import SystemFR.Freshness.

Require Import SystemFR.FVLemmas.
Require Import SystemFR.FVLemmasLists.
Require Import SystemFR.FVLemmasEval.

Require Import SystemFR.WFLemmasLists.
Require Import SystemFR.WFLemmasEval.

Require Import SystemFR.Polarity.
Require Import SystemFR.PolarityLemma.

Require Import SystemFR.NatCompare.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducible_values_rec_pos_induction:
  forall v2,
    is_nat_value v2 ->
    forall v1 theta T0 Ts t X,
      is_nat_value v1 ->
      twf T0 0 ->
      twf Ts 1 ->
      wf T0 0 ->
      wf Ts 0 ->
      is_erased_type T0 ->
      is_erased_type Ts ->
      valid_interpretation theta ->
      reducible_values theta t (T_rec v2 T0 Ts) ->
      equivalent (tlt v1 (succ v2)) ttrue ->
       ~(X ∈ pfv T0 type_var) ->
       ~(X ∈ pfv Ts type_var) ->
       ~(X ∈ support theta) ->
      (forall v,
          reducible_values theta v (topen 0 Ts (T_rec zero T0 Ts)) ->
          reducible_values theta v T0) ->
      has_polarities (topen 0 Ts (fvar X type_var)) ((X, Positive) :: nil) ->
      reducible_values theta t (T_rec v1 T0 Ts).
Proof.
  induction 1; destruct 1 as [ | v1' V1Succ ]; repeat step || t_tlt_sound;
    eauto 3 with b_inv;
    eauto 2 using equivalent_true;
    try omega.

  - repeat step || simp_red || t_star_smallstep_from_value;
       eauto 3 using smallstep_succ_zero with falsity.
    left; repeat step || find_exists || apply_any.
    apply reducibility_subst_head with X;
      repeat step || t_listutils || rewrite nat_value_fv in * by assumption;
      eauto 2 with btwf;
      eauto 2 with bwf.
    apply (reducible_rename_one _ _ _ _ _ X) in H21; steps; eauto using reducibility_is_candidate.
    eapply positive_grow; eauto 1;
      repeat step || autounfold with u_short;
      eauto using reducibility_is_candidate.
    apply IHis_nat_value with X; repeat step || apply equivalent_star || apply tlt_complete2;
      eauto with b_inv; eauto with omega.

  - repeat step || simp_red || t_star_smallstep_from_value;
      eauto 2 with berased;
      eauto 3 using smallstep_succ_zero with falsity.
    right; repeat step.
    apply (reducible_rename_one _ _ _ _ _ X) in H21; steps; eauto using reducibility_is_candidate.
    exists v1', X; steps.
    eapply positive_grow; eauto 1;
      repeat step || autounfold with u_short;
      eauto using reducibility_is_candidate.
    apply IHis_nat_value with X; repeat step || apply equivalent_star || apply tlt_complete2;
      eauto with b_inv; eauto with omega.
Qed.

Lemma reducible_values_rec_nat_value:
  forall theta v t T0 Ts,
    reducible_values theta v (T_rec t T0 Ts) ->
    exists n, is_nat_value n /\ star small_step t n.
Proof.
  repeat step || simp_red; eauto with b_inv.
Qed.

Ltac t_reducible_values_rec_nat_value :=
  match goal with
  | H: reducible_values _ _ (T_rec ?t _ _) |- _ =>
    poseNew (Mark t "reducible_values_rec_nat_value");
    pose proof (reducible_values_rec_nat_value _ _ _ _ _ H)
  end.

Ltac simp_red_nat :=
  match goal with
  | H: reducible_values _ _ T_nat |- _ => simp reducible_values in H
  end.

Lemma reducible_values_rec_pos:
  forall t1 t2 theta T0 Ts t X,
    twf T0 0 ->
    twf Ts 1 ->
    wf T0 0 ->
    wf Ts 0 ->
    is_erased_type T0 ->
    is_erased_type Ts ->
    valid_interpretation theta ->
    reducible_values theta t (T_rec t2 T0 Ts) ->
    equivalent (tlt t1 (succ t2)) ttrue ->
     ~(X ∈ pfv T0 type_var) ->
     ~(X ∈ pfv Ts type_var) ->
     ~(X ∈ support theta) ->
    reducible theta t1 T_nat ->
    (forall v,
        reducible_values theta v (topen 0 Ts (T_rec zero T0 Ts)) ->
        reducible_values theta v T0) ->
      has_polarities (topen 0 Ts (fvar X type_var)) ((X, Positive) :: nil) ->
    reducible_values theta t (T_rec t1 T0 Ts).
Proof.
  unfold reducible, reduces_to;
    repeat step || t_reducible_values_rec_nat_value || simp_red_nat.
  apply reducible_values_rec_backstep with t'; t_closer.
  eapply reducible_values_rec_pos_induction; eauto 1; steps;
    eauto using reducible_values_rec_step.
  eapply equivalent_tlt_steps; eauto 1; steps; eauto with bsteplemmas; eauto with b_inv.
Qed.
