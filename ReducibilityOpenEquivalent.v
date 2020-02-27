Require Import Coq.Strings.String.
Require Import Equations.Prop.Subterm.
Require Import Psatz.

Require Export SystemFR.ReducibilityRenaming.
Require Export SystemFR.EquivalenceLemmas2.
Require Export SystemFR.SwapTermHoles.
Require Export SystemFR.EquivalentContext.
Require Export SystemFR.OpenTOpen.

Opaque reducible_values.

Definition reducibility_open_equivalent_prop T : Prop :=
  forall T' t1 t2 theta v,
    T = open 0 T' t1 ->
    is_erased_type T' ->
    wf T' 1 ->
    pfv T' term_var = nil ->
    equivalent_terms t1 t2 ->
    reducible_values theta v T ->
    reducible_values theta v (open 0 T' t2).

Lemma reducibility_open_equivalent_induction:
  forall T t1 t2 theta v,
    reducibility_open_equivalent_prop (open 0 T t1) ->
    is_erased_type T ->
    wf T 1 ->
    pfv T term_var = nil ->
    equivalent_terms t1 t2 ->
    reducible_values theta v (open 0 T t1) ->
    reducible_values theta v (open 0 T t2).
Proof.
  unfold
    prop_until,
    prop_at,
    reducibility_open_equivalent_prop,
    get_measure;
    intros; eauto using equivalent_sym with eapply_any.
Qed.

Lemma reducibility_open_equivalent_induction_open:
  forall n o T t1 t2 theta v a,
    prop_until reducibility_open_equivalent_prop (n, o) ->
    type_nodes T < n ->
    is_erased_type T ->
    wf T 2 ->
    pfv T term_var = nil ->
    equivalent_terms t1 t2 ->
    is_erased_term a ->
    wf a 0 ->
    pfv a term_var = nil ->
    reducible_values theta v (open 0 (open 1 T t1) a) ->
    reducible_values theta v (open 0 (open 1 T t2) a).
Proof.
  unfold prop_until, prop_at, reducibility_open_equivalent_prop, get_measure;
    intros.

  rewrite swap_term_holes_open; steps;
    try solve [ top_level_unfold equivalent_terms; steps ].

  eapply H; repeat step || apply left_lex;
    eauto using equivalent_sym;
    eauto with erased wf fv;
    try solve [ repeat eauto with erased || autorewrite with bsize in * ].

  rewrite <- swap_term_holes_open; steps;
    try solve [ top_level_unfold equivalent_terms; steps ].
Qed.

Ltac reducibility_open_equivalent_induct_all :=
  (try solve [
    eapply reducibility_open_equivalent_induction; eauto 2 using equivalent_sym; eauto 2 with prop_until
  ]) ||
  (try solve [
    eapply reducibility_open_equivalent_induction_open; eauto; repeat step || autorewrite with bsize in *;
    t_closer; try lia
  ]).

Lemma reducibility_open_equivalent_arrow:
  forall m T1 T2,
    prop_until reducibility_open_equivalent_prop m ->
    prop_at reducibility_open_equivalent_prop m (T_arrow T1 T2).
Proof.
  unfold prop_at; intros; unfold reducibility_open_equivalent_prop; destruct T';
    repeat step || simp_red || t_reduces_to2 || apply_any || list_utils;
    eauto with erased;
    reducibility_open_equivalent_induct_all.
Qed.

Lemma reducibility_open_equivalent_prod:
  forall m T1 T2,
    prop_until reducibility_open_equivalent_prop m ->
    prop_at reducibility_open_equivalent_prop m (T_prod T1 T2).
Proof.
  unfold prop_at; intros; unfold reducibility_open_equivalent_prop; destruct T';
    repeat step || simp_red || t_reduces_to2 || apply_any || list_utils ||
           apply_any || (eexists; eexists; steps);
    try solve [ top_level_unfold equivalent_terms; repeat step; eauto with erased ];
    reducibility_open_equivalent_induct_all.
Qed.

Lemma reducibility_open_equivalent_sum:
  forall m T1 T2,
    prop_until reducibility_open_equivalent_prop m ->
    prop_at reducibility_open_equivalent_prop m (T_sum T1 T2).
Proof.
  unfold prop_at; intros; unfold reducibility_open_equivalent_prop; destruct T';
    repeat step || simp_red || t_reduces_to2 || list_utils;
    try solve [ left; eexists; steps; reducibility_open_equivalent_induct_all ];
    try solve [ right; eexists; steps; reducibility_open_equivalent_induct_all ].
Qed.

Lemma reducibility_open_equivalent_refine:
  forall m T p,
    prop_until reducibility_open_equivalent_prop m ->
    prop_at reducibility_open_equivalent_prop m (T_refine T p).
Proof.
  unfold prop_at; intros; unfold reducibility_open_equivalent_prop; destruct T';
    repeat step || simp_red || list_utils;
    reducibility_open_equivalent_induct_all;
    try solve [ top_level_unfold equivalent_terms; steps; eauto with wf erased ];
    eauto using equivalent_star_true, equivalent_sym, equivalent_open;
    eauto with fv.

  eapply equivalent_star_true; eauto.
  repeat rewrite (swap_term_holes_open T'2); steps;
    try solve [ top_level_unfold equivalent_terms; steps ];
    t_closer.
  apply equivalent_context; t_closing; eauto with erased fv.
Qed.

Lemma reducibility_open_equivalent_type_refine:
  forall m T1 T2,
    prop_until reducibility_open_equivalent_prop m ->
    prop_at reducibility_open_equivalent_prop m (T_type_refine T1 T2).
Proof.
  unfold prop_at; intros; unfold reducibility_open_equivalent_prop; destruct T';
    repeat step || simp_red || t_reduces_to2 || apply_any || eexists || list_utils;
    reducibility_open_equivalent_induct_all;
    eauto with erased.
Qed.

Lemma reducibility_open_equivalent_intersection:
  forall m T1 T2,
    prop_until reducibility_open_equivalent_prop m ->
    prop_at reducibility_open_equivalent_prop m (T_intersection T1 T2).
Proof.
  unfold prop_at; intros; unfold reducibility_open_equivalent_prop; destruct T';
    repeat step || simp_red || t_reduces_to2 || apply_any || eexists || list_utils;
    reducibility_open_equivalent_induct_all.
Qed.

Lemma reducibility_open_equivalent_union:
  forall m T1 T2,
    prop_until reducibility_open_equivalent_prop m ->
    prop_at reducibility_open_equivalent_prop m (T_union T1 T2).
Proof.
  unfold prop_at; intros; unfold reducibility_open_equivalent_prop; destruct T';
    repeat step || simp_red || t_reduces_to2 || apply_any || eexists || list_utils;
    try solve [ left;  reducibility_open_equivalent_induct_all ];
    try solve [ right; reducibility_open_equivalent_induct_all ].
Qed.

Lemma reducibility_open_equivalent_forall:
  forall m T1 T2,
    prop_until reducibility_open_equivalent_prop m ->
    prop_at reducibility_open_equivalent_prop m (T_forall T1 T2).
Proof.
  unfold prop_at; intros; unfold reducibility_open_equivalent_prop; destruct T';
    repeat step || simp_red || t_reduces_to2 ||
           apply_any || list_utils;
    eauto with erased.

  eapply reducibility_open_equivalent_induction_open; eauto;
    repeat step || apply_any || autorewrite with bsize in *;
    t_closer; try lia;
    reducibility_open_equivalent_induct_all.
Qed.

Lemma reducibility_open_equivalent_exists:
  forall m T1 T2,
    prop_until reducibility_open_equivalent_prop m ->
    prop_at reducibility_open_equivalent_prop m (T_exists T1 T2).
Proof.
  unfold prop_at; intros; unfold reducibility_open_equivalent_prop; destruct T';
    repeat step || simp_red || t_reduces_to2 || apply_any || eexists || list_utils;
      reducibility_open_equivalent_induct_all;
      eauto with erased.
Qed.

Lemma reducibility_open_equivalent_equiv:
  forall m t1 t2,
    prop_until reducibility_open_equivalent_prop m ->
    prop_at reducibility_open_equivalent_prop m (T_equiv t1 t2).
Proof.
  unfold prop_at; intros; unfold reducibility_open_equivalent_prop; destruct T';
    repeat step || simp_red || t_reduces_to2 || list_utils;
    eauto 6 using equivalent_trans, equivalent_sym, equivalent_context.
Qed.

Lemma reducibility_open_equivalent_abs:
  forall m T,
    prop_until reducibility_open_equivalent_prop m ->
    prop_at reducibility_open_equivalent_prop m (T_abs T).
Proof.
  unfold prop_at; intros; unfold reducibility_open_equivalent_prop; destruct T';
    repeat step || simp_red || t_reduces_to2 ||
           fv_open || list_utils || (eexists; steps; eauto) ||
          rewrite is_erased_term_tfv in * by eauto with erased;
    eauto with fv.

  rewrite <- open_topen; steps; eauto with twf erased.
  eapply reducibility_open_equivalent_induction; eauto; repeat step || rewrite open_topen;
    eauto 2 with erased step_tactic;
    eauto 2 with wf step_tactic;
    eauto 2 with fv step_tactic;
    eauto 2 with prop_until;
    eauto 2 with twf.
Qed.

Lemma open_T_rec:
  forall n T0 Ts rep,
    is_nat_value n ->
    open 0 (T_rec n T0 Ts) rep = T_rec n (open 0 T0 rep) (open 0 Ts rep).
Proof.
  repeat step || rewrite (open_none n) by eauto with wf.
Qed.

Lemma reducibility_open_equivalent_rec:
  forall m T1 T2 T3,
    prop_until reducibility_open_equivalent_prop m ->
    prop_at reducibility_open_equivalent_prop m (T_rec T1 T2 T3).
Proof.
  unfold prop_at; intros; unfold reducibility_open_equivalent_prop; destruct T';
    repeat step || list_utils || simp_red || t_reduces_to2;
    eauto with erased.

  - left; steps;
      reducibility_open_equivalent_induct_all;
      eauto 3 using equivalent_context, equivalent_star_nat with step_tactic.

  - right; exists n', X;
      repeat step || fv_open || list_utils ||
             rewrite is_erased_term_tfv in * by eauto with erased;
      eauto 4 using equivalent_star_nat, INVSucc, equivalent_context with step_tactic;
      eauto with fv.

    apply reducible_rename_rc with
        (fun t => reducible_values theta t (T_rec n' (open 0 T'2 t1) (open 0 T'3 t1)));
      repeat step || fv_open || unfold equivalent_rc || list_utils ||
             rewrite is_erased_term_tfv in * by eauto with erased;
      eauto with fv.

    + rewrite <- open_topen; steps; eauto with twf erased.
      eapply reducibility_open_equivalent_induction; try eassumption; repeat step || rewrite open_topen;
        eauto 2 with erased step_tactic;
        eauto 2 with wf step_tactic;
        eauto 2 with fv step_tactic;
        eauto 2 with prop_until;
        eauto with twf erased.

    + repeat rewrite <- open_T_rec in * by auto.
      eapply reducibility_open_equivalent_induction; try eassumption;
        repeat step || list_utils; eauto with erased wf fv.
      eapply prop_until_at; eauto.
      apply right_lex; repeat step || rewrite open_none by eauto with wf; eauto using lt_index_step.

    + repeat rewrite <- open_T_rec in * by auto.
      eapply reducibility_open_equivalent_induction; try eassumption;
        repeat step || list_utils; eauto with erased wf fv; eauto using equivalent_sym.
      eapply prop_until_at; eauto.
      apply leq_lt_measure;
        repeat step || rewrite open_none by eauto with wf;
        eauto using lt_index_step;
        try solve [ repeat autorewrite with bsize in *; eauto with erased ].
Qed.

Lemma reducibility_open_equivalent_aux:
  forall (m: measure_domain) T, prop_at reducibility_open_equivalent_prop m T.
Proof.
  induction m using measure_induction; destruct T;
    steps;
    eauto 2 using reducibility_open_equivalent_arrow;
    eauto 2 using reducibility_open_equivalent_sum;
    eauto 2 using reducibility_open_equivalent_prod;
    eauto 2 using reducibility_open_equivalent_refine;
    eauto 2 using reducibility_open_equivalent_type_refine;
    eauto 2 using reducibility_open_equivalent_intersection;
    eauto 2 using reducibility_open_equivalent_union;
    eauto 2 using reducibility_open_equivalent_forall;
    eauto 2 using reducibility_open_equivalent_exists;
    eauto 2 using reducibility_open_equivalent_equiv;
    eauto 2 using reducibility_open_equivalent_abs;
    eauto 2 using reducibility_open_equivalent_rec;
    try solve [
      unfold prop_at; intros; unfold reducibility_open_equivalent_prop; destruct T';
        repeat step
    ].
Qed.

Lemma reducibility_open_equivalent:
  forall T t1 t2 theta v,
    reducible_values theta v (open 0 T t1) ->
    valid_interpretation theta ->
    is_erased_type T ->
    wf T 1 ->
    pfv T term_var = nil ->
    equivalent_terms t1 t2 ->
    reducible_values theta v (open 0 T t2).
Proof.
  intros; eapply reducibility_open_equivalent_aux; eauto using equivalent_sym.
Qed.

Lemma reducibility_values_ltr:
  forall T t1 t2 theta v,
    reducible_values theta v (open 0 T t1) ->
    valid_interpretation theta ->
    is_erased_type T ->
    wf T 1 ->
    pfv T term_var = nil ->
    is_erased_term t1 ->
    wf t1 0 ->
    pfv t1 term_var = nil ->
    star scbv_step t1 t2 ->
    reducible_values theta v (open 0 T t2).
Proof.
  intros; eapply reducibility_open_equivalent; eauto; repeat step;
    eauto with wf erased;
    eauto using equivalent_star.
Qed.

Lemma reducibility_values_rtl:
  forall T t1 t2 theta v,
    reducible_values theta v (open 0 T t2) ->
    valid_interpretation theta ->
    is_erased_type T ->
    wf T 1 ->
    pfv T term_var = nil ->
    is_erased_term t1 ->
    wf t1 0 ->
    pfv t1 term_var = nil ->
    star scbv_step t1 t2 ->
    reducible_values theta v (open 0 T t1).
Proof.
  intros; eapply reducibility_open_equivalent; eauto; repeat step;
    eauto with wf erased;
    eauto using equivalent_sym, equivalent_star.
Qed.

Lemma reducibility_ltr:
  forall T t1 t2 theta t,
    reducible theta t (open 0 T t1) ->
    valid_interpretation theta ->
    is_erased_type T ->
    wf T 1 ->
    pfv T term_var = nil ->
    is_erased_term t1 ->
    wf t1 0 ->
    pfv t1 term_var = nil ->
    star scbv_step t1 t2 ->
    reducible theta t (open 0 T t2).
Proof.
  eauto using reducible_values_exprs, reducibility_values_ltr.
Qed.

Lemma reducibility_rtl:
  forall T t1 t2 theta t,
    reducible theta t (open 0 T t2) ->
    valid_interpretation theta ->
    is_erased_type T ->
    wf T 1 ->
    pfv T term_var = nil ->
    is_erased_term t1 ->
    wf t1 0 ->
    pfv t1 term_var = nil ->
    star scbv_step t1 t2 ->
    reducible theta t (open 0 T t1).
Proof.
  eauto using reducible_values_exprs, reducibility_values_rtl.
Qed.
