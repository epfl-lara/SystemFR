Require Import Equations.Equations.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Strings.String.
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
Require Import Termination.Trees.
Require Import Termination.HasTypeAnnotated.
Require Import Termination.TreeLists.
Require Import Termination.TypeErasure.
Require Import Termination.TypeErasureLemmas.
Require Import Termination.SubstitutionErase.
Require Import Termination.TreeLists.
Require Import Termination.TermListReducible.
Require Import Termination.NatUtils.

Require Import Termination.WellFormed.

Require Import Termination.Sets.
Require Import Termination.SetLemmas.

Require Import Termination.Equivalence.
Require Import Termination.EquivalenceLemmas.

Require Import Termination.RedTactics.
Require Import Termination.RedTactics2.
Require Import Termination.ReducibilityCandidate.
Require Import Termination.ReducibilityDefinition.
Require Import Termination.ReducibilityLemmas.
Require Import Termination.ReducibilityRules.
Require Import Termination.ReducibilityLetRules.
Require Import Termination.ReducibilityArrowRules.
Require Import Termination.ReducibilityPairRules.
Require Import Termination.ReducibilityBoolRules.
Require Import Termination.ReducibilityLetTermRules.
Require Import Termination.ReducibilityRefineRules.
Require Import Termination.ReducibilitySetOpsRules.
Require Import Termination.ReducibilityQuantRules.
Require Import Termination.ReducibilityEqualRules.
Require Import Termination.ReducibilitySubtypeRules.
Require Import Termination.ReducibilitySplitIteRule.
Require Import Termination.ReducibilitySplitMatchRule.
Require Import Termination.ReducibilitySplitRecRule.
Require Import Termination.ReducibilityNatRules.
Require Import Termination.ReducibilitySumRules.
Require Import Termination.ReducibilityFixRules.
Require Import Termination.ReducibilityPolymorphism.
Require Import Termination.ReducibilityRecRules.
Require Import Termination.ReducibilityRecGenRules.
Require Import Termination.ReducibilityPrimitiveSizeRules.

Require Import Termination.StrictPositivity.
Require Import Termination.StrictPositivityLemmas.
Require Import Termination.StrictPositivityErased.

Require Import Termination.WFLemmas.
Require Import Termination.WFLemmasTyping.

Require Import Termination.TWFLemmas.
Require Import Termination.TWFLemmasTyping.

Require Import Termination.FVLemmas.
Require Import Termination.FVLemmasTyping.
Require Import Termination.FVLemmasTyping2.
Require Import Termination.FVLemmasContext.

Require Import Termination.NatCompare.
Require Import Termination.NatCompareErase.

Require Import Termination.LVarOperations.
Require Import Termination.LVarOperationsErase.
Require Import Termination.NoTypeFVarErased.

Require Import Termination.BaseType.
Require Import Termination.BaseTypeLemmas.
Require Import Termination.BaseTypeSyntaxLemmas.
Require Import Termination.BaseTypeErase.

Opaque reducible_values.
Opaque Nat.eq_dec.
Opaque makeFresh.
Opaque tlt.
Opaque annotated_tlt.

(*
Ltac t_smallstep_infer :=
  match goal with
  | H: small_step ?t1 ?t2, H2: satisfies reducible_values _ ?l |- _ =>
    poseNew (Mark (l) "substitute_value");
    unshelve epose proof (small_step_subst t1 t2 l _ _ _)
  end.
*)

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
  | H: ?x = ?p -> False |- _ => apply reducible_refine with x p
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
  - apply open_reducible_app; auto.
  - apply open_reducible_type_abs with X; eauto; side_conditions.
  - rewrite erase_type_topen; repeat step || t_annotations. apply open_reducible_inst; side_conditions.
  - apply open_reducible_forall_inst; side_conditions.
  - eapply open_reducible_pp; auto.
  - eapply open_reducible_pi1; eauto.
  - eapply open_reducible_pi2; auto.
  - apply open_reducible_unit.
  - apply open_reducible_ttrue.
  - apply open_reducible_tfalse.
  - apply open_reducible_ite with x; side_conditions.
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
  - eapply open_reducible_singleton; side_conditions.
  - eapply open_reducible_equal; side_conditions.
  - apply open_reducible_intersection; side_conditions.
  - apply open_reducible_union_elim with (erase_type T1) (erase_type T2) z; slow_side_conditions.
  - apply open_reducible_refl; side_conditions.
  - apply open_reducible_forall with x (erase_type A); steps; side_conditions.
  - apply open_reducible_exists_elim with (erase_type U) (erase_type V) x y; slow_side_conditions.
  - apply open_reducible_unfold_zero2 with (erase_type Ts) (erase_term n); side_conditions.
  - rewrite erase_type_topen; repeat step || t_annotations. apply open_reducible_unfold2; unfold spositive; side_conditions.
  - apply open_reducible_unfold_in with (erase_term n) (erase_type T0) (erase_type Ts) p1 p2 pn y;
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
  - apply open_reducible_sum_match with y p; side_conditions.
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
  - eapply reducible_subtype_let_open2; eauto; many_tactics.
  - simp_red; steps.
  - simp_red; steps; t_closer.
  - simp_red; steps.
  - simp_red; steps.
  - simp_red; steps; t_closer.
  - simp_red; steps; t_closer.
  - eapply reducible_subtype_forall; eauto.
  - eapply reducible_subtype_exists; eauto.
  - eapply reducible_values_rec_equivalent; eauto with berased.

  (* equality *)
  - eauto 2 with b_equiv.
  - apply reducibility_equivalent_weaken with theta (erase_context gamma) x (erase_type T); side_conditions.
  - eauto using equivalent_trans.
  - apply equivalent_sym; eauto.
(*  - apply equivalent_step; apply small_step_subst; eauto with values bwf. *)
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

