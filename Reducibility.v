Require Import Equations.Equations.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Require Import Termination.Syntax.
Require Import Termination.Typing.
Require Import Termination.Tactics.
Require Import Termination.AssocList.
Require Import Termination.StarRelation.
Require Import Termination.TermList.
Require Import Termination.Freshness.
Require Import Termination.SubstitutionLemmas.
Require Import Termination.SmallStep.
Require Import Termination.SmallStepSubstitutions.
Require Import Termination.StarLemmas.
Require Import Termination.StarInversions.
Require Import Termination.Freshness.
Require Import Termination.ListUtils.
Require Import Termination.TermForm.

Require Import Termination.Sets.
Require Import Termination.SetLemmas.

Require Import Termination.Equivalence.
Require Import Termination.EquivalenceLemmas.

Require Import Termination.RedTactics.
Require Import Termination.ReducibilityCandidate.
Require Import Termination.ReducibilityDefinition.
Require Import Termination.ReducibilityLemmas.
Require Import Termination.ReducibilityRules.
Require Import Termination.ReducibilityLetRules.
Require Import Termination.ReducibilityRefineRules.
Require Import Termination.ReducibilityPairRules.
Require Import Termination.ReducibilityArrowRules.
Require Import Termination.ReducibilityBoolRules.
Require Import Termination.ReducibilityLetTermRules.
Require Import Termination.ReducibilitySetOpsRules.
Require Import Termination.ReducibilityQuantRules.
Require Import Termination.ReducibilityEqualRules.
Require Import Termination.ReducibilitySubtypeRules.
Require Import Termination.ReducibilitySplitIteRule.
Require Import Termination.ReducibilityNatRules.
Require Import Termination.ReducibilitySplitMatchRule.
Require Import Termination.ReducibilitySplitRecRule.

Require Import Termination.WFLemmas.
Require Import Termination.WFLemmasTyping.

Require Import Termination.FVLemmas.
Require Import Termination.FVLemmasTyping.
Require Import Termination.FVLemmasTyping2.
Require Import Termination.FVLemmasContext.

Opaque reducible_values.
Opaque Nat.eq_dec.
Opaque makeFresh.

Ltac t_smallstep_infer :=
  match goal with
  | H: small_step ?t1 ?t2, H2: satisfies reducible_values _ ?l |- _ =>
    poseNew (Mark (l) "substitute_value");
    unshelve epose proof (small_step_subst t1 t2 l _ _ _)
  end.

Ltac unfold_open :=
  repeat step || unfold open_reducible in * || t_instantiate_sat3.

Ltac unfold_all :=
  unfold equivalent, open_reducible, reducible, reduces_to in *.

Ltac unfold_reduce :=
  unfold open_reducible, reducible, reduces_to in *.

Ltac side_conditions := try eassumption; eauto with bwf; eauto with bfv; eauto 5 with bfv2.

Ltac choose_variables :=
  match goal with
  | H: NoDup (?n :: ?y :: ?p :: nil) |- _ => apply open_reducible_rec with n y p
  | H: ?n = ?p -> False |- _ => apply open_reducible_match with n p
  | H: ?x = ?p -> False |- _ => apply reducible_refine with x p
  | H: ?x = ?p -> False |- _ => apply open_reducible_let with x p
  end.

Ltac choose_variables_exists_elim :=
  match goal with
  | H: ?x = ?p -> False |- _ => apply open_reducible_exists_elim with x p
  end.

Ltac choose_variables_subtype :=
  match goal with
  | x: nat,
    H: reducible_values ?theta _
                        (T_arrow (psubstitute ?A1 _ term_var)
                                 (psubstitute ?A2 _ term_var)) |- _ =>
    eapply reducible_arrow_subtype_subst with A1 A2 _ x
  end.

Ltac slow_side_conditions :=
  try eassumption;
  repeat step || t_wf_info || p_fv || t_sets || t_context_fv || t_listutils;
    eauto 3 with bwf;
    eauto 3 with bfv2.

Ltac many_tactics :=
  repeat simp_red || unfold_all || step || t_instantiate_sat3 || t_deterministic_star || t_invert_star ||
         rewrite substitute_open || t_values_info2 || t_values_info3 ||
         t_context_right || step_inversion is_context.

Ltac split_tactic :=
  repeat step || t_wf_info_IT || t_context_fv || t_context_right || t_listutils ||
    step_inversion is_context || p_fv || t_sets.


Theorem reducibility_lemma:
  (forall tvars gamma t T,
    has_type tvars gamma t T ->
    open_reducible tvars gamma t T) /\
  (forall tvars gamma T,
    is_type tvars gamma T -> True) /\
  (forall tvars gamma,
    is_context tvars gamma -> True) /\
  (forall tvars gamma T1 T2,
    is_subtype tvars gamma T1 T2 ->
     forall theta l,
      valid_interpretation theta ->
      satisfies (reducible_values theta) gamma l ->
      support theta = tvars ->
      forall t,
        reducible_values theta t (substitute T1 l) ->
        reducible_values theta t (substitute T2 l)
  ) /\
  (forall tvars gamma t1 t2,
    are_equal tvars gamma t1 t2 ->
    (forall theta l,
       valid_interpretation theta ->
       satisfies (reducible_values theta) gamma l ->
       support theta = tvars ->
       equivalent (substitute t1 l) (substitute t2 l))
  ).
Proof.
  apply mut_HT_IT_IC_IS_AE; steps.

  (* typing *)
  - apply open_reducible_var; auto.
  - apply open_reducible_weaken; side_conditions.
  - eapply open_reducible_lambda; steps; side_conditions.
  - apply open_reducible_app; auto.
  - eapply open_reducible_pp; auto.
  - eapply open_reducible_pi1; eauto.
  - eapply open_reducible_pi2; auto.
  - apply open_reducible_unit.
  - apply open_reducible_ttrue.
  - apply open_reducible_tfalse.
  - eapply open_reducible_ite; steps; side_conditions.
  - unfold_open; repeat step || t_instantiate_sat3;  auto 3 using not_equivalent with falsity.
  - apply open_reducible_zero.
  - apply open_reducible_succ; auto.
  - choose_variables; steps; side_conditions.
  - choose_variables; steps; side_conditions.
  - choose_variables; steps; side_conditions.
  - unfold_open; eauto using reducible_values_exprs.
  - choose_variables; steps; side_conditions.
  - eapply open_reducible_singleton; steps; eauto.
  - eapply open_reducible_equal; steps; side_conditions.
  - apply open_reducible_intersection; steps; side_conditions.
  - eapply open_reducible_union_elim; slow_side_conditions.
  - apply open_reducible_refl; steps; eauto.
  - eapply open_reducible_forall; steps; side_conditions.
  - choose_variables_exists_elim; slow_side_conditions.

  (* subtyping *)
  - steps; choose_variables_subtype; steps; side_conditions.
  - eapply subtype_arrow2 with _ x f _ T; steps; side_conditions.
  - eapply subtypeExpand; steps; side_conditions.
  - eapply reducible_prod_subtype_subst with A1 A2 x gamma; steps; side_conditions.
  - apply subtype_prod2 with (support theta) gamma T x; steps; side_conditions.
  - apply reducible_refine_subtype with (support theta) gamma A p x; steps; side_conditions.
  - simp_red; steps; eauto.
  - simp_red; steps; eauto.
  - apply reducible_refine_subtype2 with gamma T x; steps; side_conditions.
  - apply reducible_refine_subtype3 with (support theta) gamma A b x p; repeat t_subset_open || slow_side_conditions.
  - unfold_all; repeat step || simp_red || t_instantiate_sat3 || t_deterministic_star.
  - apply reducible_subtype_let_left with (support theta) gamma t A B x p; steps; side_conditions.
  - simp_red; unfold_reduce; repeat step || t_termlist || eexists; eauto using equivalence_def.
  - many_tactics; eauto with bwf.
  - eapply reducible_subtype_let_open2; eauto.
  - simp_red; steps.
  - simp_red; steps; eauto with bwf bfv values.
  - simp_red; steps.
  - simp_red; steps.
  - simp_red; steps.
  - simp_red; steps.
  - eapply reducible_subtype_forall; eauto.
  - eapply reducible_subtype_exists; eauto.

  (* equality *)
  - eauto 2 with b_equiv.
  - eapply reducibility_equivalent_weaken; steps; eauto with bfv.
  - eauto using equivalent_trans.
  - apply equivalent_sym; eauto.
  - repeat step || t_smallstep_subst; eauto with values bwf b_equiv.
  - eapply equivalent_pair_eta; eauto.
  - many_tactics.
  - eauto with b_equiv.
  - eauto with b_equiv.
  - eauto with b_equiv.
  - eauto with b_equiv.
  - eauto with b_equiv.
  - eauto with b_equiv.
  - many_tactics.
  - many_tactics.
  - eapply reducible_equivalent_ite; slow_side_conditions.
  - eapply reducible_equivalent_match with (support theta) theta _ n p; steps; side_conditions.
  - eapply reducible_equivalent_rec with (support theta) theta  _ n p; steps; side_conditions.
  - repeat step || eapply_any; apply reducible_satisfies_weaker with T; steps; eauto with bfv btermlist.
  - apply equivalent_split_bool with (support theta) theta gamma1 gamma2 b x; steps; side_conditions.
  - apply equivalent_split_nat with (support theta) theta gamma1 gamma2 n x y; steps; side_conditions.
  - eauto using equivalent_error with step_tactic falsity.
  - apply equivalent_split_ite with (support theta) theta gamma1 gamma2 b e1 e2 e x y; split_tactic; eauto.
  - apply equivalent_split_match with (support theta) theta gamma1 gamma2 n e1 e2 e x y v; split_tactic; eauto.
  - apply equivalent_split_rec with (support theta) theta gamma1 gamma2 n e1 e2 e x y v T; split_tactic; eauto.
Qed.
