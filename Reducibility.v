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
Require Import Termination.TypeForm.

Require Import Termination.Sets.
Require Import Termination.SetLemmas.

Require Import Termination.Equivalence.
Require Import Termination.EquivalenceLemmas.

Require Import Termination.RedTactics.
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
Require Import Termination.FVLemmasOpen.
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
  repeat step || unfold open_reducible in * || tt.

Ltac unfold_all :=
  unfold equivalent, open_reducible, reducible, reduces_to in *.

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
  | H: reducible_values _ (T_arrow (substitute ?A1 _) (substitute ?A2 _)) |- _ =>
    eapply reducible_arrow_subtype_subst with A1 A2 _ _
  end.

Ltac slow_side_conditions :=
  try eassumption;
  repeat step || t_wf_info || p_fv || t_sets || t_context_fv || t_listutils;
    eauto 3 with bwf;
    eauto 3 with bfv2.

Ltac many_tactics :=
  repeat simp_red || unfold_all || step || tt || t_deterministic_star || t_invert_star ||
         rewrite substitute_open || t_values_info2 || t_values_info3 ||
         t_context_right || step_inversion is_context.

Ltac split_tactic :=
  repeat step || t_wf_info_IT || t_context_fv || t_context_right || t_listutils ||
    step_inversion is_context || p_fv || t_sets.


Theorem reducibility_lemma:
  (forall gamma t T,
    has_type gamma t T ->
    open_reducible gamma t T) /\
  (forall gamma T,
    is_type gamma T -> True) /\
  (forall gamma,
    is_context gamma -> True) /\
  (forall gamma T1 T2,
    is_subtype gamma T1 T2 ->
     forall t l,
      satisfies reducible_values gamma l ->
      reducible_values t (substitute T1 l) ->
      reducible_values t (substitute T2 l)
  ) /\
  (forall gamma t1 t2,
      are_equal gamma t1 t2 ->
      (forall l, satisfies reducible_values gamma l -> equivalent (substitute t1 l) (substitute t2 l))
  ).        
Proof.
  apply mut_HT_IT_IC_IS_AE; steps.

  (* typing *)
  - apply reducible_var; auto.
  - eapply open_reducible_weaken; side_conditions.
  - eapply open_reducible_lambda; side_conditions.
  - apply open_reducible_app; auto.
  - eapply open_reducible_pp; auto.
  - eapply open_reducible_pi1; eauto.
  - eapply open_reducible_pi2; auto.
  - apply open_reducible_unit.
  - apply open_reducible_ttrue.
  - apply open_reducible_tfalse.
  - eapply open_reducible_ite; side_conditions.
  - unfold_open; auto 4 using not_equivalent with falsity.
  - apply open_reducible_zero.
  - apply open_reducible_succ; auto.
  - choose_variables; side_conditions.
  - choose_variables; side_conditions.
  - choose_variables; side_conditions.
  - unfold_open; eauto using reducible_values_exprs.
  - choose_variables; side_conditions.
  - eapply open_reducible_singleton; eauto.
  - eapply open_reducible_equal; side_conditions.
  - apply open_reducible_intersection; side_conditions.
  - eapply open_reducible_union_elim; slow_side_conditions.
  - apply open_reducible_refl; auto.
  - eapply open_reducible_forall; side_conditions.
  - choose_variables_exists_elim; slow_side_conditions.

  (* subtyping *)
  - choose_variables_subtype; side_conditions.
  - eapply subtype_arrow2 with x f _ T; side_conditions.
  - eapply subtypeExpand; side_conditions.
  - eapply reducible_prod_subtype_subst with A1 A2 _ _; side_conditions.
  - apply subtype_prod2 with gamma T x; side_conditions.
  - apply reducible_refine_subtype with gamma A p x; side_conditions.
  - simp_red; steps; eauto.
  - simp_red; steps; eauto.
  - apply reducible_refine_subtype2 with gamma T x; side_conditions.
  - apply reducible_refine_subtype3 with gamma A b x p; repeat t_subset_open || slow_side_conditions.
  - unfold_all; repeat step || simp_red || tt || t_deterministic_star.
  - apply reducible_subtype_let_left with gamma t A B x p; side_conditions.
  - simp_red; unfold_all; repeat step || tt || eexists; eauto.
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
  - eapply reducibility_equivalent_weaken; eauto with bfv.
  - eauto using equivalent_trans.
  - apply equivalent_sym; auto.
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
  - eapply reducible_equivalent_match with _ n p; side_conditions.
  - eapply reducible_equivalent_rec with _ n p; side_conditions.
  - eauto 6 using reducible_satisfies_weaker with bfv bfv2 btermlist.
  - apply equivalent_split_bool with gamma1 gamma2 b x; side_conditions.
  - apply equivalent_split_nat with gamma1 gamma2 n x y; side_conditions.
  - eauto 3 using equivalent_error with step_tactic falsity.
  - apply equivalent_split_ite with gamma1 gamma2 b e1 e2 e x y; split_tactic.
  - apply equivalent_split_match with gamma1 gamma2 n e1 e2 e x y v; split_tactic.
  - apply equivalent_split_rec with gamma1 gamma2 n e1 e2 e x y v T; split_tactic.
Qed.
