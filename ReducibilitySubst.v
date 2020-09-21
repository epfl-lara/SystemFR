Require Import Equations.Equations.
Require Import Equations.Prop.Subterm.

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Export SystemFR.ReducibilityUnused.
Require Export SystemFR.ReducibilityIsCandidate.
Require Export SystemFR.TOpenTClose.
Require Export SystemFR.FVLemmasClose.
Require Export SystemFR.WFLemmasClose.

Require Import PeanoNat.
Require Import Psatz.

Open Scope list_scope.

Opaque makeFresh.
Opaque reducible_values.
Opaque lt.

Definition reducibility_subst_prop (U: tree) : Prop :=
 forall ρ V X v P,
    is_erased_type U ->
    wf U 0 ->
    pfv U term_var = nil ->
    twf V 0 ->
    is_erased_type V ->
    wf V 0 ->
    pfv V term_var = nil ->
    valid_interpretation ρ ->
    lookup PeanoNat.Nat.eq_dec ρ X = Some P ->
    (forall (t: tree), P t <-> [ ρ ⊨ t : V ]v) ->
    [ ρ ⊨ v : U ]v <-> [ ρ ⊨ v : psubstitute U ((X,V) :: nil) type_var ]v.

Lemma reducibility_subst_fvar:
  forall m n tag,
    prop_at reducibility_subst_prop m (fvar n tag).
Proof.
  unfold prop_at; intros; unfold reducibility_subst_prop;
    repeat step || simp_red;
    eauto with apply_any.
Qed.

Lemma reducibility_subst_induct_1:
  forall ρ U V X v P,
    reducibility_subst_prop U ->
    is_erased_type U ->
    wf U 0 ->
    pfv U term_var = nil ->
    twf V 0 ->
    is_erased_type V ->
    wf V 0 ->
    pfv V term_var = nil ->
    valid_interpretation ρ ->
    lookup PeanoNat.Nat.eq_dec ρ X = Some P ->
    (forall (t: tree), P t <-> [ ρ ⊨ t : V ]v) ->
    [ ρ ⊨ v : U ]v ->
    [ ρ ⊨ v : psubstitute U ((X,V) :: nil) type_var ]v.
Proof.
  unfold reducibility_subst_prop; intros; eauto with eapply_any.
Qed.

Lemma reducibility_subst_induct_2:
  forall ρ U V X v P,
    reducibility_subst_prop U ->
    is_erased_type U ->
    wf U 0 ->
    pfv U term_var = nil ->
    twf V 0 ->
    is_erased_type V ->
    wf V 0 ->
    pfv V term_var = nil ->
    valid_interpretation ρ ->
    lookup PeanoNat.Nat.eq_dec ρ X = Some P ->
    (forall (t: tree), P t <-> [ ρ ⊨ t : V ]v) ->
    [ ρ ⊨ v : psubstitute U ((X,V) :: nil) type_var ]v ->
    [ ρ ⊨ v : U ]v.
Proof.
  unfold reducibility_subst_prop; intros; eauto with eapply_any.
Qed.

Lemma reducibility_subst_induct_3:
  forall ρ U V X v P a,
    reducibility_subst_prop (open 0 U a) ->
    is_erased_type U ->
    wf U 1 ->
    pfv U term_var = nil ->
    twf V 0 ->
    is_erased_type V ->
    wf V 0 ->
    pfv V term_var = nil ->
    is_erased_term a ->
    wf a 0 ->
    pfv a term_var = nil ->
    valid_interpretation ρ ->
    lookup PeanoNat.Nat.eq_dec ρ X = Some P ->
    (forall (t: tree), P t <-> [ ρ ⊨ t : V ]v) ->
    [ ρ ⊨ v : open 0 U a ]v ->
    [ ρ ⊨ v : open 0 (psubstitute U ((X,V) :: nil) type_var) a ]v.
Proof.
  unfold reducibility_subst_prop; intros.
  rewrite substitute_open2 in * by
    repeat step || t_fv_red || rewrite is_erased_term_tfv in * by (steps; eauto with erased).
  eapply reducibility_subst_induct_1; eauto;
    steps; eauto with wf fv erased.
Qed.

Lemma reducibility_subst_induct_4:
  forall ρ U V X v P a,
    reducibility_subst_prop (open 0 U a) ->
    is_erased_type U ->
    wf U 1 ->
    pfv U term_var = nil ->
    twf V 0 ->
    is_erased_type V ->
    wf V 0 ->
    pfv V term_var = nil ->
    is_erased_term a ->
    wf a 0 ->
    pfv a term_var = nil ->
    valid_interpretation ρ ->
    lookup PeanoNat.Nat.eq_dec ρ X = Some P ->
    (forall (t: tree), P t <-> [ ρ ⊨ t : V ]v) ->
    [ ρ ⊨ v : open 0 (psubstitute U ((X,V) :: nil) type_var) a ]v ->
    [ ρ ⊨ v : open 0 U a ]v.
Proof.
  unfold reducibility_subst_prop; intros.
  rewrite substitute_open2 in * by
    repeat step || t_fv_red || rewrite is_erased_term_tfv in * by (steps; eauto with erased).
  eapply reducibility_subst_induct_2; eauto;
    steps; eauto with wf fv erased.
Qed.

Ltac reducibility_subst_induct_all :=
  (try solve [ eapply reducibility_subst_induct_1; eauto with prop_until ]) ||
  (try solve [ eapply reducibility_subst_induct_2; eauto with prop_until ]) ||
  (try solve [ eapply reducibility_subst_induct_3; eauto with prop_until;
                 eauto 2 with erased fv wf ]) ||
  (try solve [ eapply reducibility_subst_induct_4; eauto with prop_until;
                 eauto 2 with erased fv wf ]).

Lemma reducibility_subst_arrow:
  forall m T1 T2,
    prop_until reducibility_subst_prop m ->
    prop_at reducibility_subst_prop m (T_arrow T1 T2).
Proof.
  unfold prop_at; intros; unfold reducibility_subst_prop;
    repeat step || simp_red || t_reduces_to2 || apply_any || list_utils;
    eauto with erased;
    reducibility_subst_induct_all.
Qed.

Lemma reducibility_subst_prod:
  forall m T1 T2,
    prop_until reducibility_subst_prop m ->
    prop_at reducibility_subst_prop m (T_prod T1 T2).
Proof.
  unfold prop_at; intros; unfold reducibility_subst_prop;
    repeat step || simp_red || t_reduces_to2 || apply_any || list_utils ||
           (eexists; eexists; steps; eauto);
    eauto with erased;
    reducibility_subst_induct_all.
Qed.

Lemma reducibility_subst_sum:
  forall m T1 T2,
    prop_until reducibility_subst_prop m ->
    prop_at reducibility_subst_prop m (T_sum T1 T2).
Proof.
  unfold prop_at; intros; unfold reducibility_subst_prop;
    repeat step || simp_red || t_reduces_to2 || apply_any || list_utils;
    eauto with erased;
    try solve [ left; eexists; steps; reducibility_subst_induct_all ];
    try solve [ right; eexists; steps; reducibility_subst_induct_all ].
Qed.

Lemma reducibility_subst_refine:
  forall m T p,
    prop_until reducibility_subst_prop m ->
    prop_at reducibility_subst_prop m (T_refine T p).
Proof.
  unfold prop_at; intros; unfold reducibility_subst_prop;
    repeat step || simp_red || t_reduces_to2 || apply_any || list_utils ||
           (rewrite substitute_nothing5 in * by (steps; eauto with fv));
    reducibility_subst_induct_all.
Qed.

Lemma reducibility_subst_type_refine:
  forall m T1 T2,
    prop_until reducibility_subst_prop m ->
    prop_at reducibility_subst_prop m (T_type_refine T1 T2).
Proof.
  unfold prop_at; intros; unfold reducibility_subst_prop;
    repeat step || simp_red || t_reduces_to2 || apply_any || list_utils;
    reducibility_subst_induct_all;
    try solve [ eexists; reducibility_subst_induct_all ];
    eauto with erased.
Qed.

Lemma reducibility_subst_intersection:
  forall m T1 T2,
    prop_until reducibility_subst_prop m ->
    prop_at reducibility_subst_prop m (T_intersection T1 T2).
Proof.
  unfold prop_at; intros; unfold reducibility_subst_prop;
    repeat step || simp_red || t_reduces_to2 || apply_any || list_utils;
    reducibility_subst_induct_all.
Qed.

Lemma reducibility_subst_union:
  forall m T1 T2,
    prop_until reducibility_subst_prop m ->
    prop_at reducibility_subst_prop m (T_union T1 T2).
Proof.
  unfold prop_at; intros; unfold reducibility_subst_prop;
    repeat step || simp_red || t_reduces_to2 || apply_any || list_utils;
    try solve [ left; reducibility_subst_induct_all ];
    try solve [ right; reducibility_subst_induct_all ].
Qed.

Lemma reducibility_subst_equiv:
  forall m t1 t2,
    prop_until reducibility_subst_prop m ->
    prop_at reducibility_subst_prop m (T_equiv t1 t2).
Proof.
  unfold prop_at; intros; unfold reducibility_subst_prop;
    repeat step || simp_red || t_reduces_to2 || apply_any || list_utils ||
           (rewrite substitute_nothing5 in * by (steps; eauto with fv)).
Qed.

Lemma reducibility_subst_forall:
  forall m T1 T2,
    prop_until reducibility_subst_prop m ->
    prop_at reducibility_subst_prop m (T_forall T1 T2).
Proof.
  unfold prop_at; intros; unfold reducibility_subst_prop;
    repeat step || simp_red || t_reduces_to2 || apply_any || list_utils || t_instantiate_reducible_erased;
    eauto with erased;
    reducibility_subst_induct_all.
Qed.

Lemma reducibility_subst_exists:
  forall m T1 T2,
    prop_until reducibility_subst_prop m ->
    prop_at reducibility_subst_prop m (T_exists T1 T2).
Proof.
  unfold prop_at; intros; unfold reducibility_subst_prop;
    repeat step || simp_red || list_utils;
    try solve [ eexists; steps; eauto; reducibility_subst_induct_all ];
    eauto with erased.
Qed.

Lemma reducibility_subst_abs:
  forall m T,
    prop_until reducibility_subst_prop m ->
    prop_at reducibility_subst_prop m (T_abs T).
Proof.
  unfold prop_at; intros; unfold reducibility_subst_prop;
    repeat step || simp_red.

  - exists (makeFresh ((X :: nil) :: support ρ ::
                  pfv V type_var :: pfv T type_var ::
                  pfv (psubstitute T ((X, V) :: nil) type_var) type_var :: nil)
      ); repeat step || finisher.
    instantiate_any.
    lazymatch goal with
    | H: [ _ ⊨ _ : _ ]v |- [ (?M,?RC) :: _ ⊨ _ : _ ]v =>
      apply (reducible_rename_one _ _ _ _ _ M) in H
    end;
      repeat step || finisher || rewrite substitute_topen2.

    apply reducibility_subst_induct_1 with P;
      repeat step || apply reducible_unused2;
      eauto 3 with erased fv wf step_tactic;
      eauto with prop_until;
      eauto with apply_any;
      try finisher;
      try solve [ apply_anywhere reducible_unused3; repeat step || finisher || apply_any ].

  - exists (makeFresh ((X0 :: nil) :: (X :: nil) :: support ρ ::
                             pfv V type_var :: pfv T type_var ::
                             pfv (psubstitute T ((X, V) :: nil) type_var) type_var :: nil)
      ); repeat step || finisher.
    instantiate_any.

    lazymatch goal with
    | H: [ _ ⊨ _ : _ ]v |- [ (?M,?RC) :: _ ⊨ _ : _ ]v =>
      apply (reducible_rename_one _ _ _ _ _ M) in H
    end; repeat step || finisher.

    lazymatch goal with
    | H: [ _ ⊨ _ : _ ]v |- _ =>
      rewrite substitute_topen2 in H by repeat step || finisher
    end.

    apply reducibility_subst_induct_2 with V X P;
      repeat step || apply reducible_unused2;
      eauto 3 with erased fv wf step_tactic;
      eauto with prop_until;
      eauto with apply_any;
      try finisher;
      try solve [ apply_anywhere reducible_unused3; repeat step || finisher || apply_any ].
Qed.

Lemma subst_T_rec:
  forall n T0 Ts X V,
    is_nat_value n ->
    psubstitute (T_rec n T0 Ts) ((X,V) :: nil) type_var =
    T_rec n (psubstitute T0 ((X,V) :: nil) type_var) (psubstitute Ts ((X,V) :: nil) type_var).
Proof.
  repeat step || rewrite (substitute_nothing5 n) by eauto with fv.
Qed.

Lemma reducibility_subst_rec:
  forall m t T0 Ts,
    prop_until reducibility_subst_prop m ->
    prop_at reducibility_subst_prop m (T_rec t T0 Ts).
Proof.
  unfold prop_at; intros; unfold reducibility_subst_prop;
    repeat step || simp_red || list_utils ||
           (rewrite substitute_nothing5 in * by (steps; eauto with fv));
    eauto with erased;
    try solve [ left; steps; reducibility_subst_induct_all ].

  - right.
    unshelve eexists n', (
      makeFresh ((X :: nil) :: pfv V type_var ::
                 pfv T0 type_var :: pfv Ts type_var ::
                 pfv (psubstitute T0 ((X, V) :: nil) type_var) type_var ::
                 pfv (psubstitute Ts ((X, V) :: nil) type_var) type_var ::
                 support ρ :: nil)
    ), _, _; eauto;
      repeat step || finisher.

    lazymatch goal with
    | H: [ _ ⊨ _ : _ ]v |- [ (?M,?RC) :: _ ⊨ _ : _ ]v =>
      apply (reducible_rename_one_rc _ RC _ _ _ _ M) in H
    end; repeat step || unfold equivalent_rc || rewrite substitute_topen2;
      try finisher.

    + apply reducibility_subst_induct_1 with P;
        repeat step || apply reducible_unused2 || apply reducibility_is_candidate || list_utils ||
               (rewrite fv_subst_different_tag in * by steps);
        eauto 3 with erased fv wf step_tactic;
        eauto with prop_until;
        eauto with apply_any;
        try finisher.

      apply_anywhere reducible_unused3;
        repeat step || finisher || apply_any || apply reducibility_is_candidate || list_utils ||
               (rewrite fv_subst_different_tag in * by steps);
        eauto 2 with wf fv erased step_tactic.

    + rewrite <- subst_T_rec by auto.
      eapply reducibility_subst_induct_1; eauto;
        repeat step || list_utils; eauto with erased fv wf;
          eauto with prop_until.

    + rewrite <- subst_T_rec in * by auto.
      eapply reducibility_subst_induct_2; eauto;
        repeat step || list_utils; eauto with erased fv wf;
          eauto with prop_until.

  - right.
    unshelve eexists n', (
      makeFresh ((X :: nil) :: pfv V type_var ::
                 pfv T0 type_var :: pfv Ts type_var ::
                 pfv (psubstitute T0 ((X, V) :: nil) type_var) type_var ::
                 pfv (psubstitute Ts ((X, V) :: nil) type_var) type_var ::
                 support ρ :: nil)
    ), _, _; eauto;
      repeat step || finisher.

    lazymatch goal with
    | H: [ _ ⊨ _ : _ ]v |- [ (?M,?RC) :: _ ⊨ _ : _ ]v =>
      apply (reducible_rename_one_rc _ RC _ _ _ _ M) in H
    end; repeat step || unfold equivalent_rc || rewrite substitute_topen2;
      try finisher.

    + apply reducibility_subst_induct_2 with V X P;
        repeat step || apply reducibility_is_candidate || list_utils;
        eauto 3 with erased fv wf step_tactic;
        eauto with prop_until;
        try finisher.

      * apply reducible_unused2;
          repeat step || finisher || apply reducibility_is_candidate || list_utils;
          eauto with erased fv wf;
          eauto with apply_any.

      * apply_anywhere reducible_unused3;
          repeat step || finisher || apply_any || apply reducibility_is_candidate || list_utils ||
                 (rewrite fv_subst_different_tag in * by steps);
          eauto 2 with wf fv erased step_tactic.

      * rewrite substitute_topen2 in *; steps; try finisher.

    + rewrite <- subst_T_rec in * by auto.
      eapply reducibility_subst_induct_2; eauto;
        repeat step || list_utils; eauto with erased fv wf;
          eauto with prop_until.

    + rewrite <- subst_T_rec in * by auto.
      eapply reducibility_subst_induct_1; eauto;
        repeat step || list_utils; eauto with erased fv wf;
          eauto with prop_until.
Qed.

Lemma reducibility_subst_aux:
  forall (m: measure_domain) T, prop_at reducibility_subst_prop m T.
Proof.
  induction m using measure_induction; destruct T;
    steps;
    eauto 2 using reducibility_subst_fvar;
    eauto 2 using reducibility_subst_arrow;
    eauto 2 using reducibility_subst_prod;
    eauto 2 using reducibility_subst_sum;
    eauto 2 using reducibility_subst_refine;
    eauto 2 using reducibility_subst_type_refine;
    eauto 2 using reducibility_subst_intersection;
    eauto 2 using reducibility_subst_union;
    eauto 2 using reducibility_subst_forall;
    eauto 2 using reducibility_subst_exists;
    eauto 2 using reducibility_subst_equiv;
    eauto 2 using reducibility_subst_abs;
    eauto 2 using reducibility_subst_rec;
    try solve [
      unfold prop_at; intros; unfold reducibility_subst_prop;
        repeat step
    ].
Qed.

Lemma reducibility_subst:
  forall (ρ: interpretation) U V X v P,
    valid_interpretation ρ ->
    is_erased_type U ->
    wf U 0 ->
    pfv U term_var = nil ->
    twf V 0 ->
    is_erased_type V ->
    wf V 0 ->
    pfv V term_var = nil ->
    valid_interpretation ρ ->
    lookup PeanoNat.Nat.eq_dec ρ X = Some P ->
    (forall (t: tree), P t <-> [ ρ ⊨ t : V ]v) ->
    [ ρ ⊨ v : U ]v <-> [ ρ ⊨ v : psubstitute U ((X,V) :: nil) type_var ]v.
Proof.
  intros; eapply reducibility_subst_aux; eauto.
Qed.

Lemma reducible_values_subst_head:
  forall (ρ : interpretation) U V X v,
    [ (X, fun v => [ ρ ⊨ v : V ]v) :: ρ ⊨ v : topen 0 U (fvar X type_var) ]v ->
    valid_interpretation ρ ->
    (X ∈ pfv U type_var -> False) ->
    (X ∈ pfv V type_var -> False) ->
    is_erased_type U ->
    wf U 0 ->
    pfv U term_var = nil ->
    twf V 0 ->
    is_erased_type V ->
    wf V 0 ->
    pfv V term_var = nil ->
    [ ρ ⊨ v : topen 0 U V ]v.
Proof.
  intros.
  apply reducible_unused3 with X (fun v => [ ρ ⊨ v : V ]v);
    repeat step || fv_open  || list_utils || apply reducibility_is_candidate.

  lazymatch goal with
  | H: [ (?X,?RC) :: ?ρ ⊨ ?v : ?U ]v |- _ =>
    unshelve epose proof (proj1 (
      reducibility_subst ((X,RC) :: ρ) U V X v
                         (fun v => [ ρ ⊨ v : V ]v)
                         _ _ _ _ _ _ _ _ _ _ _) H)
  end;
    repeat step || list_utils || t_substitutions || rewrite substitute_nothing3 in *;
      eauto using reducibility_is_candidate;
      try solve [ eapply reducible_unused2; steps; eauto using reducibility_is_candidate ];
      try solve [ eapply reducible_unused3 with X _; steps; eauto using reducibility_is_candidate ];
      eauto 2 with fv wf erased step_tactic.
Qed.

Lemma reducible_values_subst_head2:
  forall (ρ : interpretation) U V X v,
    valid_interpretation ρ ->
    (X ∈ pfv U type_var -> False) ->
    (X ∈ pfv V type_var -> False) ->
    is_erased_type U ->
    wf U 0 ->
    pfv U term_var = nil ->
    twf V 0 ->
    is_erased_type V ->
    wf V 0 ->
    pfv V term_var = nil ->
    [ ρ ⊨ v : topen 0 U V ]v ->
    [ (X, fun v => [ ρ ⊨ v : V ]v) :: ρ ⊨ v : topen 0 U (fvar X type_var) ]v.
Proof.
  intros.
  apply (reducible_unused2 _ _ X _ (fun v => [ ρ ⊨ v : V ]v)) in H9;
    repeat step || fv_open  || list_utils;
    eauto using reducibility_is_candidate.

  lazymatch goal with
  | H: [ _ ⊨ _ : _ ]v |- [ (?X,?RC) :: ?ρ ⊨ ?v : ?U ]v =>
    unshelve epose proof (
      reducibility_subst ((X,RC) :: ρ) U V X v
                         (fun v => [ ρ ⊨ v : V ]v)
                         _ _ _ _ _ _ _ _ _ _ _)
  end;
    repeat step || list_utils || t_substitutions || rewrite substitute_nothing3 in *;
      eauto using reducibility_is_candidate;
      try solve [ eapply reducible_unused2; steps; eauto using reducibility_is_candidate ];
      try solve [ eapply reducible_unused3 with X _; steps; eauto using reducibility_is_candidate ];
      eauto 2 with wf fv erased step_tactic.
Qed.

Lemma reducible_subst_head2:
  forall (ρ : interpretation) U V X t,
    valid_interpretation ρ ->
    (X ∈ pfv U type_var -> False) ->
    (X ∈ pfv V type_var -> False) ->
    is_erased_type U ->
    wf U 0 ->
    pfv U term_var = nil ->
    twf V 0 ->
    is_erased_type V ->
    wf V 0 ->
    pfv V term_var = nil ->
    [ ρ ⊨ t : topen 0 U V ] ->
    [ (X, fun v => [ ρ ⊨ v : V ]v) :: ρ ⊨ t : topen 0 U (fvar X type_var) ].
Proof.
  repeat unfold reduces_to;
    repeat step;
      t_closer;
    eauto using reducible_values_subst_head2.
Qed.

Lemma reducible_values_subst_head3:
  forall ρ U V X v,
    valid_interpretation ρ ->
    (X ∈ pfv V type_var -> False) ->
    is_erased_type U ->
    wf U 0 ->
    pfv U term_var = nil ->
    twf U 0 ->
    twf V 0 ->
    is_erased_type V ->
    wf V 0 ->
    pfv V term_var = nil ->
    [ ρ ⊨ v : psubstitute U ((X, V) :: nil) type_var ]v ->
    [ (X, fun v => [ ρ ⊨ v : V ]v) :: ρ ⊨ v : U ]v.
Proof.
  intros.
  rewrite <- (topen_tclose2 U X 0);
    repeat step.

  apply reducible_values_subst_head2;
    repeat step || fv_close || rewrite topen_tclose || apply fv_close_nil;
    eauto using is_erased_type_tclose;
    eauto using wf_tclose.
Qed.

Lemma reducible_subst_head3:
  forall ρ U V X t,
    valid_interpretation ρ ->
    (X ∈ pfv V type_var -> False) ->
    is_erased_type U ->
    wf U 0 ->
    pfv U term_var = nil ->
    twf U 0 ->
    twf V 0 ->
    is_erased_type V ->
    wf V 0 ->
    pfv V term_var = nil ->
    [ ρ ⊨ t : psubstitute U ((X, V) :: nil) type_var ] ->
    [ (X, fun v => [ ρ ⊨ v : V ]v) :: ρ ⊨ t : U ].
Proof.
  repeat unfold reduces_to;
    repeat step;
      t_closer;
    eauto using reducible_values_subst_head3.
Qed.
