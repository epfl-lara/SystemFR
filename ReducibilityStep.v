Require Import Coq.Strings.String.
Require Import Equations.Prop.Subterm.

Require Export SystemFR.NatCompare.
Require Export SystemFR.ReducibilityRenaming.

Definition equivalent_types T1 T2 :=
  lift inter_reducible T1 T2 /\
  is_erased_type T1 /\
  is_erased_type T2 /\
  wf T1 0 /\
  wf T2 0.

Lemma equivalent_types_size:
  forall T1 T2,
    equivalent_types T1 T2 ->
    type_nodes T1 = type_nodes T2.
Proof.
  unfold equivalent_types; steps; eauto using lift_inter_reducible_size.
Qed.

Lemma equivalent_types_def:
  forall T1 T2,
    equivalent_types T1 T2 ->
      lift inter_reducible T1 T2 /\
      is_erased_type T1 /\
      is_erased_type T2 /\
      wf T1 0 /\
      wf T2 0.
Proof. intros; apply_any. Qed.

Ltac equivalent_types_def :=
  match goal with
  | H: equivalent_types _ _ |- _ => pose proof (equivalent_types_def _ _ H)
  end.

Lemma equivalent_types_sym:
  forall T1 T2,
    equivalent_types T1 T2 ->
    equivalent_types T2 T1.
Proof.
  unfold equivalent_types; steps; eauto using inter_reducible_sym, lift_sym.
Qed.

Definition reducibility_inter_prop T : Prop :=
  forall T' theta v,
    equivalent_types T T' ->
    valid_interpretation theta ->
      (reducible_values theta v T <-> reducible_values theta v T').

Definition reducibility_inter_prop_at m T :=
  get_measure T = m -> reducibility_inter_prop T.

Definition reducibility_inter_until (m: measure_domain): Prop :=
  forall m', m' << m -> forall T, reducibility_inter_prop_at m' T.

Lemma reducibility_inter_induction_back:
  forall T T' n o theta v,
    reducibility_inter_until (n, o) ->
    equivalent_types T T' ->
    reducible_values theta v T' ->
    valid_interpretation theta ->
    type_nodes T < n ->
    reducible_values theta v T.
Proof.
  unfold
    reducibility_inter_until,
    reducibility_inter_prop_at,
    reducibility_inter_prop,
    get_measure;
    intros.

  eapply_any; eauto; apply left_lex; auto.
Qed.

Lemma reducibility_inter_induction:
  forall T T' n o theta v,
    reducibility_inter_until (n, o) ->
    equivalent_types T T' ->
    reducible_values theta v T ->
    valid_interpretation theta ->
    type_nodes T < n ->
    reducible_values theta v T'.
Proof.
  unfold
    reducibility_inter_until,
    reducibility_inter_prop_at,
    reducibility_inter_prop,
    get_measure;
    intros.

  eapply H with _ T; eauto;
    repeat step || apply left_lex;
    try solve [ erewrite equivalent_types_size by eauto using equivalent_types_sym; auto ];
    eauto using equivalent_types_sym.
Qed.

Lemma equivalent_types_size_open:
  forall T T' a k,
    lift inter_reducible T T' ->
    is_erased_type T ->
    is_erased_type T' ->
    wf T 1 ->
    wf T' 1 ->
    is_erased_term a ->
    type_nodes (open k T' a) = type_nodes T.
Proof.
  intros;
  autorewrite with bsize in *; auto;
    eauto using lift_sym, inter_reducible_sym, lift_inter_reducible_size.
Qed.

Lemma equivalent_types_open:
  forall T T',
    lift inter_reducible T T' ->
    forall a k,
      lift inter_reducible (open k T a) (open k T' a).
Proof.
  induction 1;
    repeat step;
    eauto 6 with lift;
    eauto using lift_refl;
    eauto using inter_reducible_open with lift;
    eauto using equivalent_open with lift.
Qed.

Ltac reducibility_inter_ind :=
  match goal with
  | H: lift _ ?A ?B |- reducible_values _ _ ?A =>
    eapply (reducibility_inter_induction_back A B); eauto
  | H: lift _ ?A ?B |- reducible_values _ _ ?B =>
    eapply (reducibility_inter_induction A B); eauto

  | H: lift _ ?A ?B |- reducible_values _ _ (open 0 ?A ?a) =>
    eapply (reducibility_inter_induction_back (open 0 A a) (open 0 B a)); eauto
  | H: lift _ ?A ?B |- reducible_values _ _ (open 0 ?B ?a) =>
     eapply (reducibility_inter_induction (open 0 A a) (open 0 B a)); eauto

  | H: lift _ ?A ?B |- reducible_values _ _ (topen 0 ?A ?a) =>
    eapply (reducibility_inter_induction_back (topen 0 A a) (topen 0 B a)); eauto
  | H: lift _ ?A ?B |- reducible_values _ _ (topen 0 ?B ?a) =>
     eapply (reducibility_inter_induction (topen 0 A a) (topen 0 B a)); eauto
  end;
    repeat step || unfold equivalent_types;
      eauto with omega;
      eauto 3 with erased cbn;
      eauto 3 with wf cbn;
      eauto 3 with wft cbn;
      eauto 2 using lift_inter_reducible_topen with step_tactic;
      try solve [ autorewrite with bsize in *; eauto with omega; eauto with erased ];
      try solve [ erewrite equivalent_types_size_open; eauto with erased; eauto with omega ];
      try solve [
        eapply equivalent_types_open;
          eauto using equivalent_sym, inter_reducible_sym, lift_sym
      ].

Ltac reducibility_inter_ind2 :=
  reducibility_inter_ind;
   try solve [ apply_any; steps; reducibility_inter_ind ].

Lemma reducibility_inter_arrow:
  forall m T1 T2,
    reducibility_inter_until m ->
    reducibility_inter_prop_at m (T_arrow T1 T2).
Proof.
  unfold reducibility_inter_prop_at, reducibility_inter_prop;
    intros; equivalent_types_def;
    repeat step || simp_red || t_reduces_to2 || unfold inter_reducible in * ||
           (poseNew (Mark 0 "force_invert_lift"); force_invert lift) ||
           apply_any;
    try solve [ reducibility_inter_ind ].
Qed.

Lemma reducibility_inter_prod:
  forall m T1 T2,
    reducibility_inter_until m ->
    reducibility_inter_prop_at m (T_prod T1 T2).
Proof.
  unfold reducibility_inter_prop_at, reducibility_inter_prop;
    intros; equivalent_types_def;
    repeat step || simp_red || t_reduces_to2 || unfold inter_reducible in * ||
           (poseNew (Mark 0 "force_invert_lift"); force_invert lift) ||
           apply_any || eexists;
    try solve [ reducibility_inter_ind ].
Qed.

Lemma reducibility_inter_sum:
  forall m T1 T2,
    reducibility_inter_until m ->
    reducibility_inter_prop_at m (T_sum T1 T2).
Proof.
  unfold reducibility_inter_prop_at, reducibility_inter_prop;
    intros; equivalent_types_def;
    repeat step || simp_red || t_reduces_to2 || unfold inter_reducible in * ||
           (poseNew (Mark 0 "force_invert_lift"); force_invert lift) ||
           apply_any;
    try solve [ left; eexists; steps; reducibility_inter_ind ];
    try solve [ right; eexists; steps; reducibility_inter_ind ].
Qed.

Lemma reducibility_inter_refine:
  forall m T p,
    reducibility_inter_until m ->
    reducibility_inter_prop_at m (T_refine T p).
Proof.
  unfold reducibility_inter_prop_at, reducibility_inter_prop;
    intros; equivalent_types_def;
      repeat step || simp_red ||
             (poseNew (Mark 0 "force_invert_lift"); force_invert lift);
    try solve [ reducibility_inter_ind ];
    try solve [ top_level_unfold inter_reducible; steps ].

  - eapply equivalent_star_true; try eassumption.
    apply equivalent_sym.
    apply lift_inter_reducible_equivalent; steps;
      eauto with erased; eauto with wf;
      eauto using lift_inter_reducible_open, lift_sym, lift_refl, inter_reducible_sym.

  - eapply equivalent_star_true; try eassumption.
    apply equivalent_sym.
    apply lift_inter_reducible_equivalent; steps;
      eauto with erased; eauto with wf;
      eauto using lift_inter_reducible_open, lift_sym, lift_refl, inter_reducible_sym.
Qed.

Lemma reducibility_inter_type_refine:
  forall m T1 T2,
    reducibility_inter_until m ->
    reducibility_inter_prop_at m (T_type_refine T1 T2).
Proof.
  unfold reducibility_inter_prop_at, reducibility_inter_prop;
    intros; equivalent_types_def;
    repeat step || simp_red || t_reduces_to2 || unfold inter_reducible in * ||
           (poseNew (Mark 0 "force_invert_lift"); force_invert lift) ||
           apply_any || eexists;
    try solve [ reducibility_inter_ind ].
Qed.

Lemma reducibility_inter_intersection:
  forall m T1 T2,
    reducibility_inter_until m ->
    reducibility_inter_prop_at m (T_intersection T1 T2).
Proof.
  unfold reducibility_inter_prop_at, reducibility_inter_prop;
    intros; equivalent_types_def;
    repeat step || simp_red || t_reduces_to2 || unfold inter_reducible in * ||
           (poseNew (Mark 0 "force_invert_lift"); force_invert lift) ||
           apply_any || eexists;
    try solve [ reducibility_inter_ind ].
Qed.

Lemma reducibility_inter_union:
  forall m T1 T2,
    reducibility_inter_until m ->
    reducibility_inter_prop_at m (T_union T1 T2).
Proof.
  unfold reducibility_inter_prop_at, reducibility_inter_prop;
    intros; equivalent_types_def;
    repeat step || simp_red || t_reduces_to2 || unfold inter_reducible in * ||
           (poseNew (Mark 0 "force_invert_lift"); force_invert lift) ||
           apply_any || eexists;
    try solve [ left; reducibility_inter_ind ];
    try solve [ right; reducibility_inter_ind ].
Qed.

Lemma reducibility_inter_forall:
  forall m T1 T2,
    reducibility_inter_until m ->
    reducibility_inter_prop_at m (T_forall T1 T2).
Proof.
  unfold reducibility_inter_prop_at, reducibility_inter_prop;
    intros; equivalent_types_def;
    repeat step || simp_red || t_reduces_to2 || unfold inter_reducible in * ||
           (poseNew (Mark 0 "force_invert_lift"); force_invert lift) ||
           apply_any || eexists;
    try solve [ reducibility_inter_ind2 ].
Qed.

Lemma reducibility_inter_exists:
  forall m T1 T2,
    reducibility_inter_until m ->
    reducibility_inter_prop_at m (T_exists T1 T2).
Proof.
  unfold reducibility_inter_prop_at, reducibility_inter_prop;
    intros; equivalent_types_def;
    repeat step || simp_red || t_reduces_to2 || unfold inter_reducible in * ||
           (poseNew (Mark 0 "force_invert_lift"); force_invert lift) ||
           apply_any || eexists;
    try solve [ reducibility_inter_ind ].
Qed.

Lemma reducibility_inter_equiv:
  forall m t1 t2,
    reducibility_inter_until m ->
    reducibility_inter_prop_at m (T_equiv t1 t2).
Proof.
  unfold reducibility_inter_prop_at, reducibility_inter_prop;
    intros; equivalent_types_def;
    repeat step || simp_red || t_reduces_to2 || unfold inter_reducible in * ||
           (poseNew (Mark 0 "force_invert_lift"); force_invert lift);
  eauto 7 using equivalent_trans, lift_inter_reducible_equivalent, lift_sym, inter_reducible_sym.
Qed.

Lemma lift_inter_reducible_tfv:
  forall T1 T2 X,
    lift inter_reducible T1 T2 ->
    X ∈ pfv T1 type_var ->
    X ∈ pfv T2 type_var.
Proof.
  induction 1;
    repeat step || t_listutils || unfold inter_reducible in * ||
           rewrite is_erased_term_tfv in *.
Qed.

Lemma lift_inter_reducible_tfv2:
  forall T1 T2 X,
    lift inter_reducible T1 T2 ->
    X ∈ pfv T2 type_var ->
    X ∈ pfv T1 type_var.
Proof.
  induction 1;
    repeat step || t_listutils || unfold inter_reducible in * ||
           rewrite is_erased_term_tfv in *.
Qed.

Lemma reducibility_inter_abs:
  forall m T,
    reducibility_inter_until m ->
    reducibility_inter_prop_at m (T_abs T).
Proof.
  unfold reducibility_inter_prop_at, reducibility_inter_prop;
    intros; equivalent_types_def;
    repeat step || simp_red || t_reduces_to2 || unfold inter_reducible in * ||
           (poseNew (Mark 0 "force_invert_lift"); force_invert lift) || exists X;
    try solve [ reducibility_inter_ind ];
    eauto using lift_inter_reducible_tfv;
    eauto using lift_inter_reducible_tfv2.
Qed.

Lemma reducibility_inter_rec:
  forall m T1 T2 T3,
    reducibility_inter_until m ->
    reducibility_inter_prop_at m (T_rec T1 T2 T3).
Proof.
  unfold reducibility_inter_prop_at, reducibility_inter_prop;
    intros; equivalent_types_def;
    repeat step || simp_red || t_reduces_to2 || unfold inter_reducible in * ||
           (poseNew (Mark 0 "force_invert_lift"); force_invert lift).

  - left; steps; try reducibility_inter_ind;
        eauto 3 using equivalent_star_nat, lift_inter_reducible_equivalent with step_tactic.

  - right; exists n', X; steps;
      eauto 4 using equivalent_star_nat, lift_inter_reducible_equivalent, INVSucc with step_tactic;
      eauto using lift_inter_reducible_tfv;
      eauto using lift_inter_reducible_tfv2.

    apply reducible_rename_rc with (fun t => reducible_values theta t (T_rec n' T2 T3));
      repeat step || unfold equivalent_rc; try reducibility_inter_ind;
        eauto using reducibility_is_candidate;
        eauto using lift_inter_reducible_tfv2.

    + unshelve eapply (H _ _ (T_rec n' T2 T3) eq_refl);
        repeat step || apply leq_lt_measure ||
               rewrite lift_inter_reducible_size with T0' T2 ||
               rewrite lift_inter_reducible_size with Ts' T3;
        eauto using lt_index_step;
        try solve [
          unfold equivalent_types; steps;
            eauto using lift_refl, lift_sym, inter_reducible_sym with lift;
            eauto with erased; eauto with wf
        ].

    + unshelve eapply (H _ _ (T_rec n' T0' Ts') eq_refl);
        repeat step || apply leq_lt_measure ||
               rewrite lift_inter_reducible_size with T0' T2 ||
               rewrite lift_inter_reducible_size with Ts' T3;
        eauto using lt_index_step;
        try solve [
          unfold equivalent_types; steps;
            eauto using lift_refl, lift_sym, inter_reducible_sym with lift;
            eauto with erased; eauto with wf
        ].

  - left; steps; try reducibility_inter_ind;
        eauto using equivalent_sym, equivalent_star_nat, lift_inter_reducible_equivalent
          with step_tactic.

  - right; exists n'0, X; steps;
      eauto using equivalent_sym, equivalent_star_nat, lift_inter_reducible_equivalent, INVSucc
            with step_tactic;
      eauto using lift_inter_reducible_tfv;
      eauto using lift_inter_reducible_tfv2.

    apply reducible_rename_rc with (fun t => reducible_values theta t (T_rec n'0 T0' Ts'));
      repeat step || unfold equivalent_rc; try reducibility_inter_ind;
        eauto using reducibility_is_candidate;
        eauto using lift_inter_reducible_tfv2;
        eauto using lift_inter_reducible_tfv.

    + unshelve eapply (H _ _ (T_rec n'0 T0' Ts') eq_refl);
        repeat step || apply leq_lt_measure ||
               rewrite lift_inter_reducible_size with T0' T2 ||
               rewrite lift_inter_reducible_size with Ts' T3;
        eauto using lt_index_step;
        try solve [
          unfold equivalent_types; steps;
            eauto using lift_refl, lift_sym, inter_reducible_sym with lift;
            eauto with erased; eauto with wf
        ].

    + unshelve eapply (H _ _ (T_rec n'0 T2 T3) eq_refl);
        repeat step || apply leq_lt_measure ||
               rewrite lift_inter_reducible_size with T0' T2 ||
               rewrite lift_inter_reducible_size with Ts' T3;
        eauto using lt_index_step;
        try solve [
          unfold equivalent_types; steps;
            eauto using lift_refl, lift_sym, inter_reducible_sym with lift;
            eauto with erased; eauto with wf
        ].
Qed.

Lemma reducibility_inter_aux:
  forall (m: measure_domain) T, reducibility_inter_prop_at m T.
Proof.
  induction m using measure_induction; destruct T;
    eauto 2 using reducibility_inter_arrow;
    eauto 2 using reducibility_inter_sum;
    eauto 2 using reducibility_inter_prod;
    eauto 2 using reducibility_inter_refine;
    eauto 2 using reducibility_inter_type_refine;
    eauto 2 using reducibility_inter_intersection;
    eauto 2 using reducibility_inter_union;
    eauto 2 using reducibility_inter_forall;
    eauto 2 using reducibility_inter_exists;
    eauto 2 using reducibility_inter_equiv;
    eauto 2 using reducibility_inter_abs;
    eauto 2 using reducibility_inter_rec;
    try solve [
      unfold reducibility_inter_prop_at, reducibility_inter_prop, equivalent_types;
        steps; try force_invert lift;
        repeat step || simp_red || top_level_unfold inter_reducible
    ].
Qed.

Lemma reducibility_inter_inter:
  forall T t1 t2 theta v,
    reducible_values theta v (open 0 T t1) ->
    valid_interpretation theta ->
    is_erased_type T ->
    wf T 1 ->
    inter_reducible t1 t2 ->
    reducible_values theta v (open 0 T t2).
Proof.
  intros; eapply reducibility_inter_aux; eauto using equivalent_sym.
  unfold equivalent_types, equivalent_terms in *;
    repeat step || apply lift_inter_reducible_open;
    eauto using lift_refl;
    eauto using inter_reducible_sym with lift;
    try solve [ top_level_unfold inter_reducible; steps; eauto with erased wf ].
Qed.

Lemma reducibility_values_ltr:
  forall T t1 t2 theta v,
    reducible_values theta v (open 0 T t1) ->
    valid_interpretation theta ->
    is_erased_type T ->
    wf T 1 ->
    wf t1 0 ->
    is_erased_term t1 ->
    star scbv_step t1 t2 ->
    reducible_values theta v (open 0 T t2).
Proof.
  intros; eapply reducibility_inter_inter; eauto; repeat step || unfold inter_reducible;
    eauto with wf erased.
Qed.

Lemma reducibility_values_rtl:
  forall T t1 t2 theta v,
    reducible_values theta v (open 0 T t2) ->
    valid_interpretation theta ->
    is_erased_type T ->
    wf T 1 ->
    wf t1 0 ->
    is_erased_term t1 ->
    star scbv_step t1 t2 ->
    reducible_values theta v (open 0 T t1).
Proof.
  intros; eapply reducibility_inter_inter; eauto; repeat step || unfold inter_reducible;
    eauto with wf erased.
Qed.

Lemma reducibility_ltr:
  forall T t1 t2 theta t,
    reducible theta t (open 0 T t1) ->
    valid_interpretation theta ->
    is_erased_type T ->
    wf T 1 ->
    wf t1 0 ->
    is_erased_term t1 ->
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
    wf t1 0 ->
    is_erased_term t1 ->
    star scbv_step t1 t2 ->
    reducible theta t (open 0 T t1).
Proof.
  eauto using reducible_values_exprs, reducibility_values_rtl.
Qed.
