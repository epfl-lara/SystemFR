Require Import Equations.Equations.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import SystemFR.Syntax.
Require Import SystemFR.Typing.
Require Import SystemFR.Tactics.
Require Import SystemFR.AssocList.
Require Import SystemFR.StarRelation.
Require Import SystemFR.TermList.
Require Import SystemFR.Freshness.
Require Import SystemFR.SubstitutionLemmas.
Require Import SystemFR.SmallStep.
Require Import SystemFR.SmallStepSubstitutions.
Require Import SystemFR.StarLemmas.
Require Import SystemFR.StarInversions.
Require Import SystemFR.Freshness.
Require Import SystemFR.ListUtils.
Require Import SystemFR.Trees.
Require Import SystemFR.HasTypeAnnotated.
Require Import SystemFR.TreeLists.
Require Import SystemFR.TypeErasure.
Require Import SystemFR.TypeErasureLemmas.
Require Import SystemFR.SubstitutionErase.
Require Import SystemFR.TreeLists.
Require Import SystemFR.TermListReducible.
Require Import SystemFR.SomeTerms.

Require Import SystemFR.Sets.
Require Import SystemFR.SetLemmas.

Require Import SystemFR.Equivalence.
Require Import SystemFR.EquivalenceLemmas.

Require Import SystemFR.Polarity.
Require Import SystemFR.PolarityErase.
Require Import SystemFR.PolarityLemmas.

Require Import SystemFR.RedTactics.
Require Import SystemFR.RedTactics2.
Require Import SystemFR.ReducibilityCandidate.
Require Import SystemFR.ReducibilityDefinition.
Require Import SystemFR.ReducibilityLemmas.
Require Import SystemFR.ReducibilityRules.
Require Import SystemFR.ReducibilityLetRules.
Require Import SystemFR.ReducibilityArrowRules.
Require Import SystemFR.ReducibilityPairRules.
Require Import SystemFR.ReducibilityBoolRules.
Require Import SystemFR.ReducibilityLetTermRules.
Require Import SystemFR.ReducibilityRefineRules.
Require Import SystemFR.ReducibilitySetOpsRules.
Require Import SystemFR.ReducibilityQuantRules.
Require Import SystemFR.ReducibilityEqualRules.
Require Import SystemFR.ReducibilitySubtypeRules.
Require Import SystemFR.ReducibilitySplitIteRule.
Require Import SystemFR.ReducibilitySplitMatchRule.
Require Import SystemFR.ReducibilitySplitRecRule.
Require Import SystemFR.ReducibilityNatRules.
Require Import SystemFR.ReducibilitySumRules.
Require Import SystemFR.ReducibilityPolymorphism.
Require Import SystemFR.ReducibilityRecRules.
Require Import SystemFR.ReducibilityPrimitiveSizeRules.
Require Import SystemFR.ReducibilityFixRules.
Require Import SystemFR.ReducibilityTypeRefineRules.
Require Import SystemFR.ReducibilityRecGenRules.
Require Import SystemFR.ReducibilityIteTypeRules.
Require Import SystemFR.ReducibilityRecPos.
Require Import SystemFR.ReducibilityRecognizers.
Require Import SystemFR.ReducibilitySugar.

Require Import SystemFR.StrictPositivity.
Require Import SystemFR.StrictPositivityLemmas.
Require Import SystemFR.StrictPositivityErased.

Require Import SystemFR.WFLemmas.
Require Import SystemFR.WFLemmasLists.
Require Import SystemFR.WFLemmasTyping.

Require Import SystemFR.TWFLemmas.
Require Import SystemFR.TWFLemmasTyping.

Require Import SystemFR.FVLemmas.
Require Import SystemFR.FVLemmasTyping.
Require Import SystemFR.FVLemmasTyping2.
Require Import SystemFR.FVLemmasContext.
Require Import SystemFR.FVLemmasLists.

Require Import SystemFR.NatCompare.
Require Import SystemFR.NatCompareErase.

Require Import SystemFR.LVarOperations.
Require Import SystemFR.LVarOperationsErase.
Require Import SystemFR.NoTypeFVarErased.

Require Import SystemFR.BaseType.
Require Import SystemFR.BaseTypeLemmas.
Require Import SystemFR.BaseTypeSyntaxLemmas.
Require Import SystemFR.BaseTypeErase.

Require Import SystemFR.TypeOperations.
Require Import SystemFR.TypeOperationsLemmas.
Require Import SystemFR.TypeOperationsSyntaxLemmas.
Require Import SystemFR.TypeOperationsErase.

Opaque reducible_values.
Opaque Nat.eq_dec.
Opaque makeFresh.
Opaque tlt.
Opaque annotated_tlt.

Ltac unfold_open :=
  repeat step || unfold open_reducible in * || t_instantiate_sat3.

Ltac unfold_all :=
  unfold equivalent, open_reducible, reducible, reduces_to in *.

Ltac unfold_reduce :=
  unfold open_reducible, reducible, reduces_to in *.

Ltac t_erase_open :=
  (progress rewrite erase_type_open in * by (eauto 2 with bannot step_tactic)) ||
  (progress rewrite erase_term_open in * by (eauto 2 with bannot step_tactic)) ||
  (progress rewrite erase_type_topen in * by (eauto 2 with bannot step_tactic)) ||
  (progress rewrite erase_term_topen in * by (eauto 2 with bannot step_tactic)).

Ltac side_conditions :=
  repeat
    step || t_fv_erase || t_subset_erase || apply erase_term_wf || apply erase_type_wf ||
    (progress rewrite erase_context_append in *) ||
    (progress rewrite erased_context_support in *) || t_erase_open ||
    unshelve eauto with bwf bwft ||
    unshelve eauto with btwf ||
    unshelve eauto 3 with bfv ||
    unshelve eauto 2 with bfv2 ||
    unshelve eauto 2 with berased;
    try solve [ repeat p_fv; steps; eauto 2 using subset_transitive with sets ];
    try solve [ repeat t_wf_info; steps ].

Ltac side_conditions2 := side_conditions; side_conditions.

Ltac choose_variables :=
  match goal with
  | H: NoDup (?n :: ?y :: ?p :: nil) |- _ => apply open_reducible_rec with n y p
  | H: ?n = ?p -> False |- _ => apply open_reducible_match with n p
  | H: ?x = ?p -> False |- _ => apply open_reducible_refine with x p
  | H2: has_type _ _ ?t ?A, H: ?x = ?p -> False |- _ =>
      is_var t;
      apply open_reducible_let with (erase_type A) x p
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
  repeat step || side_conditions || t_wf_info || p_fv || t_sets || t_context_fv || t_listutils ||
         t_context_annotations;
    try solve [ eapply subset_add3; eauto ];
    eauto 3 with bwf;
    eauto 3 with bfv2;
    eauto 3 with berased.

Ltac t_invert_star2 :=
  match goal with
  | H1: is_value ?v,
    H2: star small_step (psubstitute ?v ?l ?tag) ?v2 |- _ =>
    unshelve epose proof (star_smallstep_value (psubstitute v l tag) v2 H2 _); clear H2
  end.

Ltac many_tactics :=
  repeat simp_red || unfold_all || step || t_instantiate_sat3 || t_deterministic_star || t_invert_star ||
         (progress rewrite erase_type_open in * by (eauto with bannot; eauto 2 with bannot step_tactic)) ||
         t_invert_star2 || apply is_value_subst ||
         rewrite substitute_open || t_values_info2 ||
         t_context_right || step_inversion is_context;
    try solve [ eapply reducible_values_list; eauto 2 ].

Ltac split_tactic :=
  repeat step || side_conditions || t_wf_info_IT || t_context_fv || t_context_right || t_listutils ||
    step_inversion is_context || p_fv || t_sets.

Theorem reducibility_lemma:
  (forall tvars gamma t T,
    has_type tvars gamma t T ->
    open_reducible tvars (erase_context gamma) (erase_term t) (erase_type T)) /\
  (forall tvars gamma T,
    is_type tvars gamma T -> True) /\
  (forall tvars gamma,
    is_context tvars gamma -> True) /\
  (forall tvars gamma T1 T2,
    is_subtype tvars gamma T1 T2 ->
     forall theta l,
      valid_interpretation theta ->
      satisfies (reducible_values theta) (erase_context gamma) l ->
      support theta = tvars ->
      forall t,
        reducible_values theta t (substitute (erase_type T1) l) ->
        reducible_values theta t (substitute (erase_type T2) l)
  ) /\
  (forall tvars gamma t1 t2,
    are_equal tvars gamma t1 t2 ->
    (forall theta l,
       valid_interpretation theta ->
       satisfies (reducible_values theta) (erase_context gamma) l ->
       support theta = tvars ->
       equivalent (substitute (erase_term t1) l) (substitute (erase_term t2) l))
  ).
Proof.
  apply mut_HT_IT_IC_IS_AE; steps.

  (* typing *)
  - apply open_reducible_var; auto using in_erased_context.
  - apply open_reducible_weaken; side_conditions.
  - apply open_reducible_lambda with x; side_conditions.
  - apply open_reducible_app with (erase_type U); auto.
  - apply open_reducible_type_abs with X; eauto; side_conditions.
  - rewrite erase_type_topen; repeat step || t_annotations. apply open_reducible_inst; side_conditions.
  - eapply open_reducible_forall_inst; side_conditions.
  - apply open_reducible_intersection; steps.
    eapply open_reducible_singleton; side_conditions; eauto with b_equiv.
  - eapply open_reducible_pp; auto.
  - eapply open_reducible_pi1; eauto.
  - eapply open_reducible_pi2; eauto.
  - eapply open_reducible_type_refine; eauto.
  - apply open_reducible_get_refinement_witness with (erase_term t1) (erase_type A) (erase_type B) x;
      repeat side_conditions ||
             rewrite (open_none (erase_term t2) 0) in * ||
             rewrite erase_term_open in * by (eauto 3 with bannot step_tactic).
  - apply open_reducible_unit.
  - apply open_reducible_ttrue.
  - apply open_reducible_tfalse.
  - apply open_reducible_ite with x; side_conditions.
  - apply open_reducible_T_ite_push with (erase_type T1) (erase_type T2) x; side_conditions; eauto 2 using ite_type_erase.
  - apply open_reducible_T_ite with x; side_conditions; eauto 2 using ite_type_erase.
  - apply open_reducible_is_pair; side_conditions.
  - apply open_reducible_is_succ; side_conditions.
  - apply open_reducible_is_lambda; side_conditions.
  - unfold_open; repeat step || t_instantiate_sat3;  auto 3 using not_equivalent with falsity.
  - apply open_reducible_zero.
  - apply open_reducible_succ; auto.
  - choose_variables; side_conditions.
  - apply open_reducible_fix with n y p;
      repeat side_conditions ||
             rewrite (open_none (erase_term ts) 1) in * ||
             rewrite erase_term_open in * by (eauto 3 with bannot step_tactic).
  - apply open_reducible_fix_strong_induction with n y p;
      repeat side_conditions || rewrite tlt_erase in * ||
             rewrite (open_none (erase_term ts) 1) in * ||
             rewrite erase_type_map_indices in * ||
             rewrite erase_term_open in * by (eauto 3 with bannot step_tactic).
  - choose_variables; side_conditions.
  - choose_variables; side_conditions.
  - unfold_open; tac1; eauto using reducible_values_exprs.
  - choose_variables; side_conditions.
  - apply open_reducible_let2 with (erase_type A) x p; side_conditions.
  - eapply open_reducible_singleton; side_conditions.
  - eapply open_reducible_equal; side_conditions.
  - apply open_reducible_intersection; side_conditions.
  - apply open_reducible_union_elim with (erase_type T1) (erase_type T2) z; slow_side_conditions.
  - apply open_reducible_refl; side_conditions.
  - apply open_reducible_forall with x (erase_type A); steps; side_conditions.
  - apply open_reducible_exists_elim with (erase_type U) (erase_type V) x y; slow_side_conditions.

  - apply open_reducible_unfold_zero2 with (erase_type Ts) (erase_term n); side_conditions.
  - rewrite erase_type_topen; repeat step || t_annotations. apply open_reducible_unfold2; unfold spositive; side_conditions.
  - apply open_reducible_unfold_in with (erase_term n) (erase_type T0) (erase_type Ts) p1 p2 y;
      side_conditions.
  - apply open_reducible_unfold_pos_in with (erase_term n) (erase_type T0) (erase_type Ts) p1 y;
      side_conditions.
  - apply open_reducible_fold2 with p pn; side_conditions.
  - rewrite erase_type_topen; repeat step || t_annotations.
    apply open_reducible_unfold_gen with X; side_conditions.
    change (fvar X type_var) with (erase_type (fvar X type_var)).
    rewrite <- erase_type_topen; repeat step || apply strictly_positive_erased; eauto 2 with bannot.
  - apply open_reducible_unfold_in_gen with (erase_type T0) (erase_type Ts) X p y; side_conditions.
    change (fvar X type_var) with (erase_type (fvar X type_var)).
    rewrite <- erase_type_topen; repeat step || apply strictly_positive_erased; eauto 2 with step_tactic bannot.
  - apply open_reducible_fold_gen with X; side_conditions.
    + change (fvar X type_var) with (erase_type (fvar X type_var)).
      rewrite <- erase_type_topen; repeat step || apply strictly_positive_erased;
        eauto 2 with bannot step_tactic.
    + apply H; steps. rewrite substitute_topen; steps; eauto with btwf.
  - apply open_reducible_fold_gen2 with X; side_conditions;
      eauto 3 with bwf bwft step_tactic;
      eauto 4 with btwf step_tactic.
    + change (fvar X type_var) with (erase_type (fvar X type_var)).
      rewrite <- erase_type_topen; repeat step || apply strictly_positive_erased;
        eauto 2 with bannot step_tactic.
    + change (fvar X type_var) with (erase_type (fvar X type_var)).
      rewrite <- erase_type_topen; repeat step || apply base_type_erase.
    + rewrite erase_type_topen in *; (steps; eauto 3 with bannot step_tactic).

  - apply open_reducible_left; side_conditions.
  - apply open_reducible_right; side_conditions.
  - apply open_reducible_sum_match with (erase_type A) (erase_type B) y p; side_conditions.
  - apply open_reducible_tsize with (erase_type A); side_conditions.

  (* subtyping *)
  - steps; choose_variables_subtype; side_conditions2.
  - eapply subtype_arrow2 with _ x f _ (erase_type T); steps; side_conditions; side_conditions.
  - apply subtypeExpand with (support theta) x (erase_type A) (erase_context gamma); side_conditions; side_conditions.
  - apply reducible_prod_subtype_subst with (erase_type A1) (erase_type A2) x (erase_context gamma); side_conditions.
  - apply subtype_prod2 with (support theta) (erase_context gamma) (erase_type T) x; side_conditions.
  - apply reducible_refine_subtype with (support theta) (erase_context gamma) (erase_type A) (erase_term p) x; side_conditions.
  - simp_red; steps; eauto.
  - simp_red; steps; eauto; t_closer.
  - apply reducible_refine_subtype2 with (erase_context gamma) (erase_type T) x; steps; side_conditions.
  - apply reducible_refine_subtype3 with (support theta) (erase_context gamma) (erase_type A) (erase_term b) x p; repeat t_subset_open || slow_side_conditions.
  - unfold_all; repeat step || simp_red || t_instantiate_sat3 || t_deterministic_star; t_closer.
  - apply reducible_subtype_let_left with (support theta) (erase_context gamma) (erase_term t) (erase_type A) (erase_type B) x p; side_conditions.
  - simp_red; unfold_reduce; repeat step || t_termlist || find_smallstep_value2; eauto using equivalence_def with berased.
  - many_tactics; eauto with bwf.
  - eapply reducible_subtype_let_open2; eauto; many_tactics; eauto with berased.
  - simp_red; steps.
  - simp_red; steps; t_closer.
  - simp_red; steps.
  - simp_red; steps.
  - simp_red; steps; t_closer.
  - simp_red; steps; t_closer.
  - eapply reducible_subtype_forall; eauto.
  - eapply reducible_subtype_exists; eauto.
  - eapply reducible_values_rec_equivalent; eauto with berased.
  - apply reducible_values_rec_pos with (psubstitute (erase_term n2) l term_var) X;
      eauto with berased;
        repeat side_conditions || t_instantiate_sat3 || t_pfv_in_subst || t_substitutions ||
               rewrite tlt_erase in * ||
               rewrite psubstitute_tlt in * ||
               apply_any;
        eauto using has_polarities_subst_erase.

  (* equality *)
  - eauto 2 with b_equiv.
  - apply reducibility_equivalent_weaken with theta (erase_context gamma) x (erase_type T); side_conditions.
  - eauto using equivalent_trans.
  - apply equivalent_sym; eauto.
  - apply equivalent_step; apply small_step_subst; eauto with values bwf.
  - eapply equivalent_pair_eta; eauto.
  - many_tactics; t_closer.
  - eauto with b_equiv.
  - eauto with b_equiv.
  - eauto with b_equiv.
  - eauto with b_equiv.
  - eauto with b_equiv.
  - eauto with b_equiv.
  - eauto with b_equiv.
  - eauto with b_equiv.
  - many_tactics.
  - many_tactics.
  - apply reducible_equivalent_ite with theta (support theta) (erase_context gamma) x; slow_side_conditions.
  - apply reducible_equivalent_match with (support theta) theta (erase_context gamma) n p; steps; side_conditions.
  - apply reducible_equivalent_rec with (support theta) theta (erase_context gamma) n p; steps; side_conditions.
  - repeat step || eapply_any || rewrite erase_context_append in *.
      apply reducible_satisfies_weaker with (erase_type T); side_conditions; eauto with btermlist.
  - apply equivalent_split_bool with (support theta) theta (erase_context gamma1) (erase_context gamma2) (erase_term b) x; side_conditions.
  - apply equivalent_split_nat with (support theta) theta (erase_context gamma1) (erase_context gamma2) (erase_term n) x y; steps; side_conditions.
  - eauto using equivalent_error with step_tactic falsity.
  - apply equivalent_split_ite with (support theta) theta (erase_context gamma1) (erase_context gamma2) (erase_term b) (erase_term e1) (erase_term e2) (erase_term e) x y; split_tactic; eauto.
  - apply equivalent_split_match with (support theta) theta (erase_context gamma1) (erase_context gamma2) (erase_term n) (erase_term e1) (erase_term e2) (erase_term e) x y v; split_tactic; eauto.
  - apply equivalent_split_rec with (support theta) theta (erase_context gamma1) (erase_context gamma2) (erase_term n) (erase_term e1) (erase_term e2) (erase_term e) x y v; split_tactic; eauto.
Qed.
