Require Import Equations.Equations.
Require Import Equations.Prop.Subterm.

Require Import Psatz.

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Export SystemFR.ReducibilityIsCandidate.
Require Export SystemFR.StrictPositivityLemmas.

Opaque makeFresh.
Opaque PeanoNat.Nat.eq_dec.
Opaque reducible_values.
Opaque strictly_positive.

Definition sp_push_forall_prop T: Prop :=
  forall pre_ρ ρ ρ' A v,
    wf T 0 ->
    twf T 0 ->
    wf A 0 ->
    twf A 0 ->
    valid_interpretation ρ ->
    valid_interpretation ρ' ->
    valid_pre_interpretation (fun a => [ ρ ⊨ a : A ]v) pre_ρ ->
    non_empty ρ A ->
    strictly_positive T (support ρ') ->
    is_erased_type A ->
    is_erased_type T ->
    pfv A term_var = nil ->
    pfv T term_var = nil ->
    (forall a,
      [ ρ ⊨ a : A ]v ->
      [ push_one a pre_ρ ++ ρ ⊨ v : T ]v) ->
    forall_implies (fun a => [ ρ ⊨ a : A ]v) pre_ρ ρ' ->
    [ ρ' ++ ρ ⊨ v : T ]v.

Lemma sp_push_forall_fvar: forall m n f, prop_at sp_push_forall_prop m (fvar n f).
Proof.
  unfold prop_at, sp_push_forall_prop;
  unfold push_all, push_one;
  intros;
  instantiate_non_empty;
    repeat match goal with
           | _ => step || simp_red || t_instantiate_reducible ||
                 rewrite support_map_values in * || list_utils
           | _ => t_lookup_same || t_lookupor || t_lookup_rewrite || t_lookupMap2 || t_lookup
           | _ => t_forall_implies_apply || t_forall_implies_support
           end.
Qed.

Hint Immediate sp_push_forall_fvar: b_push.

Lemma sp_push_forall_prop_inst:
  forall T pre_ρ ρ ρ' A v,
    sp_push_forall_prop T ->
    wf T 0 ->
    twf T 0 ->
    wf A 0 ->
    twf A 0 ->
    valid_interpretation ρ ->
    valid_interpretation ρ' ->
    valid_pre_interpretation (fun a => [ ρ ⊨ a : A ]v) pre_ρ ->
    non_empty ρ A ->
    strictly_positive T (support ρ') ->
    is_erased_type A ->
    is_erased_type T ->
    pfv A term_var = nil ->
    pfv T term_var = nil ->
    (forall a,
      [ ρ ⊨ a : A ]v ->
      [ push_one a pre_ρ ++ ρ ⊨ v : T ]v) ->
    forall_implies (fun a => [ ρ ⊨ a : A ]v) pre_ρ ρ' ->
    [ ρ' ++ ρ ⊨ v : T ]v.
Proof.
  unfold sp_push_forall_prop; steps; eauto.
Qed.

Ltac t_reduces_to3 :=
  match goal with
  | H1: [ _ ⊨ ?a : ?A ]v,
    H2: forall a, _ -> _ -> _ ->
            [ ?ρ ⊨ a : ?A ]v ->
            reduces_to (fun t => [ ?ρ ⊨ t : open 0 ?T _ ]v) _
      |- reduces_to _ _ =>
    poseNew (Mark (H1,H2) "t_reduces_to2");
    apply reduces_to_equiv with (fun t => [ ρ ⊨ t : open 0 T a ]v)
  end.

Ltac rewrite_support :=
  match goal with
  | H: support _ = support _ |- _ => rewrite H in *
  end.

Lemma reducible_unused_many_push_one:
  forall P T pre_ρ ρ ρ' v a,
    [ ρ' ++ ρ ⊨ v : T ]v ->
    forall_implies P pre_ρ ρ' ->
    no_type_fvar T (support ρ') ->
    [ push_one a pre_ρ ++ ρ ⊨ v : T ]v.
Proof.
  repeat step || rewrite reducible_unused_many in * || rewrite support_push_one ||
         t_forall_implies_support || rewrite_support.
Qed.

Ltac t_instantiate_reducible2 :=
  match goal with
  | H0: no_type_fvar ?T (support ?ρ'),
    H1: [ _ ⊨ ?v : ?T ]v,
    H3: forall a, _ -> _ -> _ -> [ push_one _ ?pre_ρ ++ ?ρ ⊨ a : ?T ]v -> _,
    H4: forall_implies _ ?pre_ρ ?ρ'
    |- _ => poseNew (Mark (v, H3) "t_instantiate_reducible2");
          unshelve epose proof (H3 v _ _ _ _)
  end.

Ltac find_exists3 :=
  match goal with
  | H: [ _ ⊨ ?v : ?T ]v
    |- exists x, [ _ ⊨ x : ?T ]v =>
    exists v
  end.

Lemma reduces_to_value:
  forall ρ T t v,
    reduces_to (fun v => [ ρ ⊨ v : T ]v) t ->
    valid_interpretation ρ ->
    cbv_value v ->
    t ~>* v ->
    [ ρ ⊨ v : T ]v.
Proof.
  unfold reduces_to;
    repeat step || t_deterministic_star;
    eauto using red_is_val.
Qed.

Lemma sp_push_forall_arrow:
  forall m T1 T2,
    prop_until sp_push_forall_prop m ->
    prop_at sp_push_forall_prop m (T_arrow T1 T2).
Proof.
  unfold prop_at; intros; unfold sp_push_forall_prop; intros; instantiate_non_empty;
    repeat step || simp_red || simp_spos || list_utils ||
           t_instantiate_reducible || t_instantiate_reducible2 ||
           unfold reduces_to in *;
    eauto 2 using reducible_unused_many_push_one.

  eexists; steps; try eassumption.

  apply sp_push_forall_prop_inst with pre_ρ A;
    repeat step || apply strictly_positive_open ||
           t_instantiate_reducible || t_instantiate_reducible2 || simp_red;
    eauto with prop_until;
    eauto with wf twf erased fv;
    eauto 2 using reducible_unused_many_push_one.

  eapply reduces_to_value; eauto using red_is_val with b_valid_interp.
  unfold reduces_to; steps.
  exists v1; steps.
Qed.

Hint Immediate sp_push_forall_arrow: b_push.

Lemma sp_push_forall_prod:
  forall m T1 T2, prop_until sp_push_forall_prop m -> prop_at sp_push_forall_prop m (T_prod T1 T2).
Proof.
  unfold prop_at; intros; unfold sp_push_forall_prop; intros; instantiate_non_empty;
    repeat step || simp_red || simp_spos || list_utils || t_instantiate_reducible || t_instantiate_reducible2 ||
           unfold reduces_to in *;
    eauto 2 using reducible_unused_many_push_one.

  eexists; eexists; steps;
    repeat step.

  - apply sp_push_forall_prop_inst with pre_ρ A; steps; eauto with prop_until.
    repeat step || t_instantiate_reducible || t_instantiate_reducible2 || simp_red.

  - apply sp_push_forall_prop_inst with pre_ρ A;
      repeat step || apply strictly_positive_open; eauto with prop_until;
      eauto with wf fv twf erased.
    repeat step || t_instantiate_reducible || t_instantiate_reducible2 || simp_red.
Qed.

Hint Immediate sp_push_forall_prod: b_push.

Lemma sp_push_forall_sum:
  forall m T1 T2, prop_until sp_push_forall_prop m -> prop_at sp_push_forall_prop m (T_sum T1 T2).
Proof.
  unfold prop_at; intros; unfold sp_push_forall_prop; intros; instantiate_non_empty;
    repeat step || simp_red || simp_spos || list_utils || t_instantiate_reducible.

  - left; eexists; steps.
    apply sp_push_forall_prop_inst with pre_ρ A; steps; eauto with prop_until.
    repeat step || t_instantiate_reducible || t_instantiate_reducible2 || simp_red.

  - right; eexists; steps.
    apply sp_push_forall_prop_inst with pre_ρ A; steps; eauto with prop_until.
    repeat step || t_instantiate_reducible || t_instantiate_reducible2 || simp_red.
Qed.

Hint Immediate sp_push_forall_sum: b_push.

Lemma sp_push_forall_refine:
  forall m T b, prop_until sp_push_forall_prop m -> prop_at sp_push_forall_prop m (T_refine T b).
Proof.
  unfold prop_at; intros; unfold sp_push_forall_prop; intros; instantiate_non_empty;
    repeat step || simp_red || simp_spos || t_instantiate_reducible || list_utils.

  apply sp_push_forall_prop_inst with pre_ρ A; steps; eauto with prop_until.
  repeat step || t_instantiate_reducible || t_instantiate_reducible2 || simp_red.
Qed.

Hint Immediate sp_push_forall_refine: b_push.

Lemma reducible_unused_many_push_one2:
  forall P T pre_ρ ρ ρ' v a,
    [ push_one a pre_ρ ++ ρ ⊨ v : T ]v ->
    forall_implies P pre_ρ ρ' ->
    no_type_fvar T (support ρ') ->
    [ ρ' ++ ρ ⊨ v : T ]v.
Proof.
  intros.
  rewrite reducible_unused_many; steps.
  rewrite reducible_unused_many in *;
    repeat step || rewrite support_push_one || t_forall_implies_support || rewrite_support.
Qed.

Lemma sp_push_forall_type_refine:
  forall m T1 T2,
    prop_until sp_push_forall_prop m ->
    prop_at sp_push_forall_prop m (T_type_refine T1 T2).
Proof.
  unfold prop_at; intros; unfold sp_push_forall_prop; intros; instantiate_non_empty;
    repeat step || simp_red || simp_spos || t_instantiate_reducible || list_utils;
    eauto using reducible_unused_many_push_one2.

  exists p; eapply reducible_unused_many_push_one2; eauto.
  apply no_type_fvar_open; t_closer.
Qed.

Hint Immediate sp_push_forall_type_refine: b_push.

Lemma sp_push_forall_intersection:
  forall m T1 T2,
    prop_until sp_push_forall_prop m ->
    prop_at sp_push_forall_prop m (T_intersection T1 T2).
Proof.
  unfold prop_at; intros; unfold sp_push_forall_prop; intros; instantiate_non_empty;
    repeat step || simp_red || simp_spos || t_instantiate_reducible || list_utils.
  - apply sp_push_forall_prop_inst with pre_ρ A; steps; eauto with prop_until.
    repeat step || t_instantiate_reducible || t_instantiate_reducible2 || simp_red.
  - apply sp_push_forall_prop_inst with pre_ρ A; steps; eauto with prop_until.
    repeat step || t_instantiate_reducible || t_instantiate_reducible2 || simp_red.
Qed.

Hint Immediate sp_push_forall_intersection: b_push.

Lemma sp_push_forall_union:
  forall m T1 T2,
    prop_until sp_push_forall_prop m ->
    prop_at sp_push_forall_prop m (T_union T1 T2).
Proof.
  unfold prop_at; intros; unfold sp_push_forall_prop; intros; instantiate_non_empty;
    repeat step || simp_red || simp_spos || list_utils || t_instantiate_reducible;
    eauto using reducible_unused_many_push_one2.
Qed.

Hint Immediate sp_push_forall_union: b_push.

Lemma sp_push_forall_forall:
  forall m T1 T2, prop_until sp_push_forall_prop m -> prop_at sp_push_forall_prop m (T_forall T1 T2).
Proof.
  unfold prop_at; intros; unfold sp_push_forall_prop; intros; instantiate_non_empty;
    repeat step || simp_red || simp_spos || list_utils || t_instantiate_reducible;
    eauto using reducible_unused_many_push_one2.

  apply sp_push_forall_prop_inst with pre_ρ A;
    repeat step || apply strictly_positive_open; eauto with prop_until;
      eauto with wf fv twf erased.
  repeat step || t_instantiate_reducible || t_instantiate_reducible2 || simp_red;
    eauto using reducible_unused_many_push_one.
Qed.

Hint Immediate sp_push_forall_forall: b_push.

Lemma sp_push_forall_exists:
  forall m T1 T2, prop_until sp_push_forall_prop m -> prop_at sp_push_forall_prop m (T_exists T1 T2).
Proof.
  unfold prop_at; intros; unfold sp_push_forall_prop; intros; instantiate_non_empty;
    repeat step || simp_red || simp_spos || t_instantiate_reducible || list_utils.

  exists a0; steps;
    eauto using reducible_unused_many_push_one2.
  eapply reducible_unused_many_push_one2; eauto.
  apply no_type_fvar_open; t_closer.
Qed.

Hint Immediate sp_push_forall_exists: b_push.

Lemma sp_push_forall_abs:
  forall m T, prop_until sp_push_forall_prop m -> prop_at sp_push_forall_prop m (T_abs T).
Proof.
  unfold prop_at; intros; unfold sp_push_forall_prop; intros; instantiate_non_empty;
    repeat step || simp_red || simp_spos || t_instantiate_reducible || list_utils.

  exists (makeFresh (
         support ρ ::
         support pre_ρ ::
         support ρ' ::
         pfv A type_var ::
         pfv T type_var ::
         nil));
    repeat step || finisher || t_instantiate_rc || find_smallstep_value || list_utils;
    t_closer.

  lazymatch goal with
  | |- reducible_values ((?X,?RC) :: ?g1 ++ ?g2) _ (topen 0 ?T ?rep) =>
    apply reducible_rename with (topen 0 T rep) (g1 ++ (X,RC) :: g2)
                                (idrel (X :: support g1 ++ support g2 ++ pfv T type_var))
  end;
    repeat step || apply valid_interpretation_append || t_deterministic_star ||
           apply push_all_is_candidate || apply equivalent_with_relation_permute ||
           apply equal_with_relation_refl2 ||
           rewrite idrel_lookup || fv_open ||
           rewrite idrel_lookup_swap || fv_open ||
           list_utils;
      eauto with b_valid_interp;
      try solve [ unfold equivalent_rc; steps; eauto ];
      try finisher;
      eauto with b_red_is_val.

  apply sp_push_forall_prop_inst with pre_ρ A;
    repeat
      step || t_valid_interpretation_equiv || t_forall_implies_equiv ||
      (progress autorewrite with bsize in * ) ||
      apply strictly_positive_swap ||
      apply twf_topen ||
      apply is_erased_type_topen ||
      apply non_empty_extend ||
      t_deterministic_star ||
      apply strictly_positive_topen ||
      apply wf_topen;
    try finisher;
    eauto 1 with prop_until;
    eauto with wf twf lia erased;
    eauto 2 with fv step_tactic;
    eauto 2 using red_is_val with step_tactic;
    eauto with b_red_is_val;
    try solve [ apply_any; assumption ].

  + apply reducible_unused2; steps; try finisher; eauto with apply_any.
  + apply reducible_unused3 in H25; repeat step; try finisher; eauto with apply_any.
  + apply reducible_unused3 in H25;
      repeat step || t_instantiate_reducible || t_deterministic_star ||
             t_instantiate_rc || simp_red || unfold reduces_to in *;
      try finisher; eauto with apply_any;
        eauto with b_red_is_val.
    apply reducible_rename_permute with X1; repeat step || rewrite support_push_one in *;
      eauto with b_valid_interp;
      try finisher.
  + apply reducible_unused2; steps; try finisher; eauto with apply_any.
  + apply reducible_unused3 in H25; steps; try finisher; eauto with apply_any.
Qed.

Hint Immediate sp_push_forall_abs: b_push.

Lemma sp_push_forall_rec:
  forall m n T0 Ts, prop_until sp_push_forall_prop m -> prop_at sp_push_forall_prop m (T_rec n T0 Ts).
Proof.
  unfold prop_at; intros; unfold sp_push_forall_prop; intros; instantiate_non_empty;
    repeat step || simp_red || simp_spos || t_instantiate_reducible || list_utils.

  (** Cases where the variables do not appear **)
  - left; steps; eauto 2 using reducible_unused_many_push_one2.

  - right.
      exists n', (makeFresh (
                       support ρ ::
                       support pre_ρ ::
                       support ρ' ::
                       pfv A type_var ::
                       pfv T0 type_var ::
                       pfv Ts type_var ::
                       pfv n' type_var ::
                       nil));
      repeat step || simp_red || list_utils ||
             t_instantiate_reducible ||
             t_deterministic_star ||
             topen_none;
        eauto with lia;
        try finisher.

        repeat rewrite reducible_unused_middle in * by (
          repeat step || list_utils || t_forall_implies_support || rewrite_support ||
                 apply valid_interpretation_append ||
                 (eapply valid_interpretation_one; eauto) ||
                 apply no_type_fvar_in_topen ||
                 rewrite support_push_one in * ||
                 rewrite support_push_all in * ||
                 apply reducibility_is_candidate;
          try solve [ apply_any; assumption ];
          try finisher;
          eauto with wf fv erased
        ).

      eapply reducible_rename_one_rc; eauto;
        repeat step ||
               apply reducibility_is_candidate ||
               unfold equivalent_rc;
        eauto with b_valid_interp apply_any;
        try finisher.

      + eapply reducible_unused_many_push_one2; eauto; unfold no_type_fvar in *; repeat step || list_utils;
          eauto with fv.
        rewrite is_erased_term_tfv in *; steps; eauto with erased.
      + eapply reducible_unused_many_push_one; eauto; unfold no_type_fvar in *; repeat step || list_utils;
          eauto with fv.
        rewrite is_erased_term_tfv in *; steps; eauto with erased.

  (** Cases where the recursive variable appears strictly positively **)

  - left; steps.
    apply sp_push_forall_prop_inst with pre_ρ A; steps; eauto with prop_until.
    repeat step || t_instantiate_reducible || t_instantiate_reducible2 || simp_red || t_deterministic_star.

  - right.
      exists n', (makeFresh (
                       support ρ ::
                       support pre_ρ ::
                       support ρ' ::
                       pfv A type_var ::
                       pfv T0 type_var ::
                       pfv Ts type_var ::
                       pfv n' type_var ::
                       nil));
      repeat step || simp_red || list_utils ||
             t_instantiate_reducible ||
             t_deterministic_star ||
             topen_none;
        eauto with lia;
        try finisher.

      rewrite app_comm_cons.
      lazymatch goal with
      | H1: non_empty ?ρ ?A,
        H2: forall_implies _ ?pre_ρ ?ρ' |-
          reducible_values (((?X, fun t => [ ?ρ' ++ ?ρ ⊨ t : ?R ]v) :: ?ρ') ++ ?ρ) _ ?T =>
          apply H with (get_measure T) ((X, fun a t => [ push_one a pre_ρ ++ ρ ⊨ t : R ]v) :: pre_ρ) A
      end;
        repeat
          step || list_utils || apply left_lex || autorewrite with bsize in * || t_deterministic_star ||
          apply is_erased_type_topen || t_instantiate_reducible ||
          apply wf_topen || apply twf_topen || apply reducibility_is_candidate ||
          (poseNew (Mark 0 "strictly_positive_topen2"); apply strictly_positive_topen2);
        try lia;
        eauto with b_valid_interp;
        try finisher;
        eauto with erased wf fv;
        eauto 2 with fv step_tactic.

      + eapply strictly_positive_rename_one; eauto;
          repeat step;
          try finisher.
      + simp reducible_values in H36;
          repeat step || t_deterministic_star.
        eapply reducible_rename_one; eauto;
          repeat step; eauto using reducibility_is_candidate with b_valid_interp;
            try finisher.
      + (* We apply one last time the induction hypothesis for rec(n) *)
        apply sp_push_forall_prop_inst with pre_ρ A;
          repeat step || list_utils || simp_spos; eauto with prop_until;
          eauto with wf twf fv erased.
Qed.

Hint Immediate sp_push_forall_rec: b_push.

Lemma strictly_positive_push_forall_aux: forall (m: measure_domain) T, prop_at sp_push_forall_prop m T.
Proof.
  induction m using measure_induction; destruct T;
    eauto 2 with b_push;
    try solve [
      unfold prop_at, sp_push_forall_prop; intros; instantiate_non_empty; repeat step || simp_red || t_instantiate_reducible
    ].
Qed.

Lemma strictly_positive_push_forall: forall T, sp_push_forall_prop T.
Proof.
  intros.
  eapply strictly_positive_push_forall_aux; eauto 1.
Qed.
