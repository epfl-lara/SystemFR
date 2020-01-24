Require Import Equations.Prop.Subterm.

Require Import Coq.Strings.String.

Require Export SystemFR.ReducibilityOpenEquivalent.

Opaque loop.
Opaque reducible_values.

Definition reducibility_equivalent_prop T : Prop :=
  forall v1 v2 theta,
    equivalent_terms v1 v2 ->
    cbv_value v2 ->
    is_erased_type T ->
    wf T 0 ->
    pfv T term_var = nil ->
    valid_interpretation theta ->
    reducible_values theta v1 T ->
    reducible_values theta v2 T.

Lemma reducibility_equivalent_nat:
  forall m, prop_at reducibility_equivalent_prop m T_nat.
Proof.
  unfold prop_at;
    repeat step || simp_red || unfold reducibility_equivalent_prop.

  apply_anywhere equivalent_sym.
  apply_anywhere equivalent_value_nat; steps.
Qed.

Lemma reducibility_equivalent_unit:
  forall m, prop_at reducibility_equivalent_prop m T_unit.
Proof.
  unfold prop_at;
    repeat step || simp_red || unfold reducibility_equivalent_prop;
    eauto using equivalent_value_unit.
Qed.

Lemma reducibility_equivalent_bool:
  forall m, prop_at reducibility_equivalent_prop m T_bool.
Proof.
  unfold prop_at;
    repeat step || simp_red || unfold reducibility_equivalent_prop.

  - apply_anywhere equivalent_sym.
    apply_anywhere equivalent_value_true; repeat step.

  - apply_anywhere equivalent_sym.
    apply_anywhere equivalent_value_false; repeat step.
Qed.

Lemma reducibility_equivalent_fvar:
  forall m n f, prop_at reducibility_equivalent_prop m (fvar n f).
Proof.
  unfold prop_at, reducibility_equivalent_prop; intros; destruct_tag;
    repeat step || simp_red;
    try solve [ eapply in_valid_interpretation_equiv; eauto ].
Qed.

Lemma equivalent_normalizing:
  forall e1 e2 v1,
    equivalent_terms e1 e2 ->
    star scbv_step e1 v1 ->
    cbv_value v1 ->
    exists v2,
      cbv_value v2 /\
      star scbv_step e2 v2.
Proof.
  intros.
  equivalence_instantiate (lvar 0 term_var);
    unfold scbv_normalizing in *; steps;
      eauto.
Qed.

Ltac equivalent_normalizing :=
  match goal with
  | H1: equivalent_terms ?e1 ?e2,
    H2: star scbv_step ?e1 ?v1 |- _ =>
    poseNew (Mark (H1, H2) "equivalent_normalizing");
    unshelve epose proof (equivalent_normalizing _ _ _ H1 H2 _)
  end.

Lemma reducibility_equivalent_inst:
  forall theta T v1 v2,
    equivalent_terms v1 v2 ->
    reducibility_equivalent_prop T ->
    valid_interpretation theta ->
    is_erased_type T ->
    wf T 0 ->
    pfv T term_var = nil ->
    reducible_values theta v1 T ->
    cbv_value v2 ->
    reducible_values theta v2 T.
Proof.
  unfold reducibility_equivalent_prop;
    repeat step; eauto.
Qed.

Lemma reducibility_equivalent_reduces_to:
  forall theta T e1 e2,
    reduces_to (fun v => reducible_values theta v T) e1 ->
    equivalent_terms e1 e2 ->
    reducibility_equivalent_prop T ->
    valid_interpretation theta ->
    is_erased_type T ->
    wf T 0 ->
    pfv T term_var = nil ->
    reduces_to (fun v => reducible_values theta v T) e2.
Proof.
  unfold reducibility_equivalent_prop, reduces_to;
    repeat step || equivalent_normalizing;
    try solve [ unfold equivalent_terms, closed_term in *; repeat step || destruct_and ];
    eauto using red_is_val.

  exists v2; steps.
  eapply_any; steps; try eassumption.
  apply equivalent_trans with e1.
  - apply equivalent_sym; equivalent_star; t_closer.
  - apply equivalent_trans with e2; auto;
      equivalent_star; unfold equivalent_terms in *; repeat step || destruct_and.
Qed.

Lemma reducibility_equivalent_prop_until_inst_size:
  forall n1 n2 T,
    prop_until reducibility_equivalent_prop (n1, n2) ->
    type_nodes T < n1 ->
    reducibility_equivalent_prop T.
Proof.
  intros; eapply prop_until_at; eauto.
  apply left_lex; auto.
Qed.

Lemma reducibility_equivalent_prop_until_inst_size2:
  forall T T',
    prop_until reducibility_equivalent_prop (get_measure T') ->
    type_nodes T < type_nodes T' ->
    reducibility_equivalent_prop T.
Proof.
  intros; eapply prop_until_at; eauto.
  apply left_lex; auto.
Qed.

Lemma reducibility_equivalent_prop_until_inst_size3:
  forall T T' a,
    prop_until reducibility_equivalent_prop (get_measure T') ->
    is_erased_type T ->
    is_erased_term a ->
    type_nodes T < type_nodes T' ->
    reducibility_equivalent_prop (open 0 T a).
Proof.
Proof.
  intros; eapply prop_until_at; eauto.
  apply left_lex.
  autorewrite with bsize; auto.
Qed.

Lemma reducibility_equivalent_arrow:
  forall m T1 T2,
    prop_until reducibility_equivalent_prop m ->
    prop_at reducibility_equivalent_prop m (T_arrow T1 T2).
Proof.
  unfold prop_at;
    repeat step || simp_red || t_reduces_to2 || t_instantiate_reducible ||
           unfold reducibility_equivalent_prop || list_utils;
    t_closer.

  eapply reducibility_equivalent_reduces_to; eauto;
    eauto using equivalent_app_left with wf fv;
    eauto 3 using reducibility_equivalent_prop_until_inst_size3 with lia step_tactic;
    eauto with erased fv.
Qed.

Lemma reducibility_equivalent_prod:
  forall m T1 T2,
    prop_until reducibility_equivalent_prop m ->
    prop_at reducibility_equivalent_prop m (T_prod T1 T2).
Proof.
  unfold prop_at;
    repeat step || list_utils || simp_red || t_reduces_to2 || t_instantiate_reducible ||
           unfold reducibility_equivalent_prop;
    t_closer.

  apply_anywhere equivalent_value_pair; steps; eauto with values.
  eexists; eexists; steps;
    try solve [ unfold equivalent_terms in *; steps; t_closer ].

  - eapply reducibility_equivalent_inst; eauto; steps;
      eauto 3 using reducibility_equivalent_prop_until_inst_size2 with lia step_tactic.

  - eapply reducibility_equivalent_inst; eauto; steps;
      eauto 3 using reducibility_equivalent_prop_until_inst_size3 with lia step_tactic;
      eauto with erased fv wf;
      eauto using reducibility_open_equivalent.
Qed.

Lemma reducibility_equivalent_sum:
  forall m T1 T2,
    prop_until reducibility_equivalent_prop m ->
    prop_at reducibility_equivalent_prop m (T_sum T1 T2).
Proof.
  unfold prop_at;
    repeat step || list_utils || simp_red || t_reduces_to2 || t_instantiate_reducible ||
           unfold reducibility_equivalent_prop;
    t_closer.

  - apply_anywhere equivalent_value_left; steps; eauto with values.
    left; eexists; steps.
    eapply reducibility_equivalent_inst;
      eauto 3 using reducibility_equivalent_prop_until_inst_size2 with lia step_tactic.

  - apply_anywhere equivalent_value_right; steps; eauto with values.
    right; eexists; steps.
    eapply reducibility_equivalent_inst;
      eauto 3 using reducibility_equivalent_prop_until_inst_size2 with lia step_tactic.
Qed.

Lemma reducibility_equivalent_refine:
  forall m T p,
    prop_until reducibility_equivalent_prop m ->
    prop_at reducibility_equivalent_prop m (T_refine T p).
Proof.
  unfold prop_at;
    repeat step || list_utils || simp_red || t_reduces_to2 || t_instantiate_reducible ||
           unfold reducibility_equivalent_prop;
    t_closer.

  - eapply reducibility_equivalent_inst; eauto; steps;
      eauto 3 using reducibility_equivalent_prop_until_inst_size2 with lia step_tactic.

  - eapply equivalent_star_true; eauto using equivalent_context.
Qed.

Lemma reducibility_equivalent_type_refine:
  forall m T1 T2,
    prop_until reducibility_equivalent_prop m ->
    prop_at reducibility_equivalent_prop m (T_type_refine T1 T2).
Proof.
  unfold prop_at;
    repeat step || list_utils || simp_red || t_reduces_to2 || t_instantiate_reducible ||
           unfold reducibility_equivalent_prop;
    t_closer.

  - eapply reducibility_equivalent_inst; eauto; steps;
      eauto 3 using reducibility_equivalent_prop_until_inst_size2 with lia step_tactic.

  - eexists; steps; eauto using reducibility_open_equivalent.
Qed.

Lemma reducibility_equivalent_union:
  forall m T1 T2,
    prop_until reducibility_equivalent_prop m ->
    prop_at reducibility_equivalent_prop m (T_union T1 T2).
Proof.
  unfold prop_at;
    repeat step || list_utils || simp_red || t_reduces_to2 || t_instantiate_reducible ||
           unfold reducibility_equivalent_prop;
    t_closer.

  - left; eapply reducibility_equivalent_inst; eauto; steps;
      eauto 3 using reducibility_equivalent_prop_until_inst_size2 with lia step_tactic.
  - right; eapply reducibility_equivalent_inst; eauto; steps;
      eauto 3 using reducibility_equivalent_prop_until_inst_size2 with lia step_tactic.
Qed.

Lemma reducibility_equivalent_intersection:
  forall m T1 T2,
    prop_until reducibility_equivalent_prop m ->
    prop_at reducibility_equivalent_prop m (T_intersection T1 T2).
Proof.
  unfold prop_at;
    repeat step || list_utils || simp_red || t_reduces_to2 || t_instantiate_reducible ||
           unfold reducibility_equivalent_prop;
    t_closer.

  - eapply reducibility_equivalent_inst; eauto; steps;
      eauto 3 using reducibility_equivalent_prop_until_inst_size2 with lia step_tactic.
  - eapply reducibility_equivalent_inst; eauto; steps;
      eauto 3 using reducibility_equivalent_prop_until_inst_size2 with lia step_tactic.
Qed.

Lemma reducibility_equivalent_equiv:
  forall m t1 t2,
    prop_until reducibility_equivalent_prop m ->
    prop_at reducibility_equivalent_prop m (T_equiv t1 t2).
Proof.
  unfold prop_at;
    repeat step || list_utils || simp_red ||
           unfold reducibility_equivalent_prop;
    t_closer.

  eapply_anywhere equivalent_value_unit; auto.
Qed.

Lemma reducibility_equivalent_forall:
  forall m T1 T2,
    prop_until reducibility_equivalent_prop m ->
    prop_at reducibility_equivalent_prop m (T_forall T1 T2).
Proof.
  unfold prop_at;
    repeat step || list_utils || simp_red || t_reduces_to2 || t_instantiate_reducible ||
           unfold reducibility_equivalent_prop;
    t_closer.

  eapply reducibility_equivalent_inst; eauto; steps;
    eauto 3 using reducibility_equivalent_prop_until_inst_size2 with lia step_tactic;
    eauto with erased fv wf;
    eauto with prop_until.
Qed.

Lemma reducibility_equivalent_exists:
  forall m T1 T2,
    prop_until reducibility_equivalent_prop m ->
    prop_at reducibility_equivalent_prop m (T_exists T1 T2).
Proof.
  unfold prop_at;
    repeat step || unfold reducibility_equivalent_prop || simp_red || list_utils.

  - t_closer.
  - eexists; steps; eauto;
    eapply reducibility_equivalent_inst; eauto; steps;
      eauto 3 using reducibility_equivalent_prop_until_inst_size2 with lia step_tactic;
      eauto with erased fv wf;
      eauto with prop_until.
Qed.

Lemma reducibility_equivalent_abs:
  forall m T,
    prop_until reducibility_equivalent_prop m ->
    prop_at reducibility_equivalent_prop m (T_abs T).
Proof.
  unfold prop_at;
    repeat step || unfold reducibility_equivalent_prop || simp_red || list_utils;
    t_closer.

  exists X; steps.
  eapply reducibility_equivalent_inst; eauto; steps;
    eauto 3 using reducibility_equivalent_prop_until_inst_size2 with lia step_tactic;
    eauto 2 with erased fv wf step_tactic;
    eauto with prop_until.
Qed.

Lemma reducibility_equivalent_rec:
  forall m t T0 Ts,
    prop_until reducibility_equivalent_prop m ->
    prop_at reducibility_equivalent_prop m (T_rec t T0 Ts).
Proof.
  unfold prop_at;
    repeat step || unfold reducibility_equivalent_prop || simp_red || list_utils;
    t_closer.

  - left; steps; eapply reducibility_equivalent_inst; eauto; steps;
      eauto with prop_until.

  - right; eexists; eexists; steps; eauto.
    eapply reducibility_equivalent_inst; eauto; repeat step || unfold reducibility_candidate;
      eauto 2 with wf fv erased step_tactic;
      eauto with prop_until;
      t_closer.

    eapply reducibility_equivalent_inst; eauto; repeat step || list_utils;
      t_closer.

    eapply prop_until_at; eauto; steps.
    apply right_lex; steps; eauto using lt_index_step.
Qed.

Lemma reducibility_equivalent_aux:
  forall (m: measure_domain) T, prop_at reducibility_equivalent_prop m T.
Proof.
  induction m using measure_induction; destruct T;
    eauto 2 using reducibility_equivalent_fvar;
    eauto 2 using reducibility_equivalent_unit;
    eauto 2 using reducibility_equivalent_bool;
    eauto 2 using reducibility_equivalent_nat;
    eauto 2 using reducibility_equivalent_prod;
    eauto 2 using reducibility_equivalent_arrow;
    eauto 2 using reducibility_equivalent_sum;
    eauto 2 using reducibility_equivalent_refine;
    eauto 2 using reducibility_equivalent_type_refine;
    eauto 2 using reducibility_equivalent_union;
    eauto 2 using reducibility_equivalent_intersection;
    eauto 2 using reducibility_equivalent_forall;
    eauto 2 using reducibility_equivalent_exists;
    eauto 2 using reducibility_equivalent_abs;
    eauto 2 using reducibility_equivalent_rec;
    eauto 2 using reducibility_equivalent_equiv;
    try solve [ unfold prop_at, reducibility_equivalent_prop; repeat step || simp_red; t_closer ].
Qed.

Lemma reducibility_equivalent:
  forall T v1 v2 theta,
    equivalent_terms v1 v2 ->
    cbv_value v2 ->
    is_erased_type T ->
    wf T 0 ->
    pfv T term_var = nil ->
    valid_interpretation theta ->
    reducible_values theta v1 T ->
    reducible_values theta v2 T.
Proof.
  intros; eapply reducibility_equivalent_aux; eauto.
Qed.
