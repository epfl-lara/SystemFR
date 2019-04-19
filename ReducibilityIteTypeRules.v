Require Import Equations.Equations.
Require Import Equations.Subterm.

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import SystemFR.Syntax.
Require Import SystemFR.Tactics.
Require Import SystemFR.SmallStep.
Require Import SystemFR.StarInversions.
Require Import SystemFR.StarRelation.
Require Import SystemFR.StarLemmas.
Require Import SystemFR.Equivalence.
Require Import SystemFR.EquivalenceLemmas.
Require Import SystemFR.ListUtils.
Require Import SystemFR.AssocList.
Require Import SystemFR.Freshness.
Require Import SystemFR.TermList.
Require Import SystemFR.SubstitutionLemmas.
Require Import SystemFR.SubstitutionErase.
Require Import SystemFR.TreeLists.
Require Import SystemFR.TermListReducible.
Require Import SystemFR.ErasedTermLemmas.

Require Import SystemFR.Sets.
Require Import SystemFR.SetLemmas.


Require Import SystemFR.WFLemmas.
Require Import SystemFR.WFLemmasEval.
Require Import SystemFR.WFLemmasLists.

Require Import SystemFR.TWFLemmas.

Require Import SystemFR.FVLemmas.
Require Import SystemFR.FVLemmasEval.
Require Import SystemFR.FVLemmasLists.

Require Import SystemFR.ReducibilityCandidate.
Require Import SystemFR.ReducibilityDefinition.
Require Import SystemFR.ReducibilityLemmas.
Require Import SystemFR.ReducibilityMeasure.
Require Import SystemFR.ReducibilityRenaming.
Require Import SystemFR.ReducibilityRecRules.
Require Import SystemFR.RedTactics.

Require Import SystemFR.TypeOperations.
Require Import SystemFR.TypeOperationsSyntaxLemmas.
Require Import SystemFR.TypeOperationsLemmas.

Require Import SystemFR.SizeLemmas.

Require Import Omega.

Opaque reducible_values.
Opaque makeFresh.

Lemma star_smallstep_ite_inv_true:
  forall b t1 t2 v,
    is_value v ->
    star small_step (ite b t1 t2) v ->
    star small_step b ttrue ->
    star small_step t1 v.
Proof.
  repeat step || t_invert_star || t_deterministic_star.
Qed.

Lemma star_smallstep_ite_inv_false:
  forall b t1 t2 v,
    is_value v ->
    star small_step (ite b t1 t2) v ->
    star small_step b tfalse ->
    star small_step t2 v.
Proof.
  repeat step || t_invert_star || t_deterministic_star.
Qed.

Ltac t_invert_ite :=
  match goal with
  | H1: star small_step (ite ?b ?t1 ?t2) ?v |- star small_step ?t1 ?v =>
      apply star_smallstep_ite_inv_true with b t2
  | H1: star small_step (ite ?b ?t1 ?t2) ?v |- star small_step ?t2 ?v =>
      apply star_smallstep_ite_inv_false with b t1
  end.

Lemma star_smallstep_ite_true:
  forall b t1 t2 v,
    star small_step b ttrue ->
    star small_step t1 v ->
    star small_step (ite b t1 t2) v.
Proof.
  eauto using star_smallstep_trans with smallstep bsteplemmas.
Qed.

Lemma star_smallstep_ite_false:
  forall b t1 t2 v,
    star small_step b tfalse ->
    star small_step t2 v ->
    star small_step (ite b t1 t2) v.
Proof.
  eauto using star_smallstep_trans with smallstep bsteplemmas.
Qed.

Ltac t_reduces_to_open :=
  match goal with
  | _: is_erased_term ?b,
    H: forall a, _ -> _ -> reduces_to (fun t => reducible_values ?theta t (open 0 ?T _)) _ |-
        reduces_to _ _ =>
        poseNew (Mark 0 "reduces_to_equiv");
        apply reduces_to_equiv with (fun t => reducible_values theta t (open 0 T b))
  end.

Lemma pfv_smallstep_ite:
  forall b t1 t2 v,
    star small_step (ite b t1 t2) v ->
    pfv b term_var = nil ->
    pfv t2 term_var = nil ->
    pfv t1 term_var = nil ->
    pfv v term_var = nil.
Proof.
  intros.
  eapply fv_star_smallstep_nil; eauto 1; repeat step || t_listutils.
Qed.

Hint Immediate pfv_smallstep_ite: bfv.

Ltac t_dangerous_rec_choice :=
  match goal with
  | H: star small_step _ zero |- _ \/ _ => left
  | H: star small_step _ (succ _) |- _ => right
  end.

Ltac find_exists_open :=
  match goal with
  | H1: reducible_values ?theta ?a ?A,
    H2: reducible_values ?theta ?v (open 0 ?B ?a)
      |- exists a _, reducible_values ?theta a _ /\ reducible_values ?theta ?v (open 0 _ a)
        => exists a
  end.

Ltac t_apply_ih :=
  match goal with
  | IH: forall _ _ _ _ _ _, _, H1: T_ite ?b ?T1 ?T2 ?T, H2: reducible_values ?theta ?v ?T1
    |- reducible_values ?theta ?v ?T =>
     is_var T;
     poseNew (Mark T "applying IH");
     unshelve eapply (IH (size T1, index T1) _ b T1 T2 T); eauto
  | IH: forall _ _ _ _ _ _, _, H1: T_ite ?b ?T1 ?T2 ?T, H2: reducible_values ?theta ?v ?T
    |- reducible_values ?theta ?v ?T1 =>
     is_var T;
     poseNew (Mark T "applying IH");
     unshelve eapply (IH (size T1, index T1) _ b T1 T2 T); eauto
  | IH: forall _ _ _ _ _ _, _, H1: T_ite ?b ?T1 ?T2 ?T, H2: reducible_values ?theta ?v (open 0 ?T1 ?a)
    |- reducible_values ?theta ?v (open 0 ?T ?a) =>
     is_var T;
     poseNew (Mark T "applying IH");
     unshelve eapply (IH (size (open 0 T1 a), index (open 0 T1 a)) _ b (open 0 T1 a) (open 0 T2 a) (open 0 T a)); eauto
  | IH: forall _ _ _ _ _ _, _, H1: T_ite ?b ?T1 ?T2 ?T, H2: reducible_values ?theta ?v (open 0 ?T ?a)
    |- reducible_values ?theta ?v (open 0 ?T1 ?a) =>
     is_var T;
     poseNew (Mark T "applying IH");
     unshelve eapply (IH (size (open 0 T1 a), index (open 0 T1 a)) _ b (open 0 T1 a) (open 0 T2 a) (open 0 T a)); eauto
  | IH: forall _ _ _ _ _ _, _, H1: T_ite ?b ?T1 ?T2 ?T, H2: forall a, _ -> _ -> reducible_values ?theta ?v (open 0 ?T1 a)
    |- reducible_values ?theta ?v (open 0 ?T ?a) =>
     is_var T;
     poseNew (Mark T "applying IH");
     unshelve eapply (IH (size (open 0 T1 a), index (open 0 T1 a)) _ b (open 0 T1 a) (open 0 T2 a) (open 0 T a)); eauto
  | IH: forall _ _ _ _ _ _, _, H1: T_ite ?b ?T1 ?T2 ?T, H2: forall a, _ -> _ -> reducible_values ?theta ?v (open 0 ?T a)
    |- reducible_values ?theta ?v (open 0 ?T1 ?a) =>
     is_var T;
     poseNew (Mark T "applying IH");
     unshelve eapply (IH (size (open 0 T1 a), index (open 0 T1 a)) _ b (open 0 T1 a) (open 0 T2 a) (open 0 T a)); eauto
  end.

Ltac t_apply_ih_topen :=
  lazymatch goal with
  | IH: forall _ _ _ _ _ _, _, H1: T_ite ?b ?T1 ?T2 ?T, H2: reducible_values ?theta ?v (topen 0 ?T1 ?X)
    |- reducible_values ?theta ?v (topen 0 ?T ?X) =>
     unshelve eapply (IH (size (topen 0 T1 X), index (topen 0 T1 X)) _ b (topen 0 T1 X) (topen 0 T2 X) (topen 0 T X)); eauto
  | IH: forall _ _ _ _ _ _, _, H1: T_ite ?b ?T1 ?T2 ?T, H2: reducible_values ?theta ?v (topen 0 ?T ?X)
    |- reducible_values ?theta ?v (topen 0 ?T1 ?X) =>
     unshelve eapply (IH (size (topen 0 T1 X), index (topen 0 T1 X)) _ b (topen 0 T1 X) (topen 0 T2 X) (topen 0 T X)); eauto
  end.

Ltac t_apply_ih_rec :=
  lazymatch goal with
  | IH: forall _ _ _ _ _ _, _, H1: T_ite ?b ?T0' ?T0'' ?T0, H2: T_ite ?b ?Ts' ?Ts'' ?Ts, H3: reducible_values ?theta ?v (T_rec ?n ?T0 ?Ts)
    |- reducible_values ?theta ?v (T_rec ?n ?T0' ?Ts') =>
     unshelve eapply (IH (size (T_rec n T0' Ts'), index (T_rec n T0' Ts')) _ b
                         (T_rec n T0' Ts') (T_rec n T0'' Ts'') (T_rec (ite b n n) T0 Ts)); eauto
  | IH: forall _ _ _ _ _ _, _, H1: T_ite ?b ?T0' ?T0'' ?T0, H2: T_ite ?b ?Ts' ?Ts'' ?Ts, H3: reducible_values ?theta ?v (T_rec ?n ?T0' ?Ts')
    |- reducible_values ?theta ?v (T_rec ?n ?T0 ?Ts) =>
     apply reducible_values_rec_equivalent with (ite b n n); eauto with b_equiv; steps; eauto with berased;
     unshelve eapply (IH (size (T_rec n T0' Ts'), index (T_rec n T0' Ts')) _ b
                         (T_rec n T0' Ts') (T_rec n T0'' Ts'') (T_rec (ite b n n) T0 Ts)); eauto
  end.

Lemma reducible_values_T_ite_true_aux:
  forall measure b T1 T2 T theta v,
    (size T1, index T1) = measure ->
    T_ite b T1 T2 T ->
    wf b 0 ->
    wf T1 0 ->
    wf T2 0 ->
    pfv b term_var = nil ->
    pfv T1 term_var = nil ->
    pfv T2 term_var = nil ->
    is_erased_term b ->
    is_erased_type T1 ->
    is_erased_type T2 ->
    star small_step b ttrue ->
    valid_interpretation theta ->
    (reducible_values theta v T <-> reducible_values theta v T1).
Proof.
  induction measure using measure_induction; intros; try omega.
  inversion H1;
    repeat match goal with
           | |- reduces_to _ _ => t_reduces_to_open
           | |- reduces_to _ _ => apply_any
           | H: forall a, _ -> _ -> reducible_values ?theta ?v (open 0 ?B a)
               |- reducible_values ?theta ?v (open 0 ?B ?a) => apply H
           | H1: T_ite _ ?A1 _ ?A, H2: reducible_values _ ?v ?A |- reducible_values _ ?v ?A1 \/ _ => left
           | H1: T_ite _ ?A1 _ ?A, H2: reducible_values _ ?v ?A1 |- reducible_values _ ?v ?A \/ _ => left
           | H1: T_ite _ ?A1 _ ?A, H2: reducible_values _ ?v ?A |- _ \/ reducible_values _ ?v ?A1 => right
           | H1: T_ite _ ?A1 _ ?A, H2: reducible_values _ ?v ?A1 |- _ \/ reducible_values _ ?v ?a => right
           | _ => step || t_apply_ih || t_dangerous_rec_choice || find_exists_open ||
                 simp_red || apply wf_open || apply fv_nils_open ||
                 t_invert_ite ||
                 t_listutils ||
                 (progress autorewrite with bsize in *) ||
                 find_smallstep_value2 || find_exists || (rewrite (open_none b) by assumption)
           end;
    t_closer;
    eauto 2 using star_smallstep_ite_true;
    eauto 2 using star_smallstep_ite_false;
    eauto 2 with b_equiv;
    eauto 2 with bwf step_tactic;
    try omega;
    eauto using ite_type_open;
    eauto with bwf bfv berased;
    try solve [ apply left_lex; autorewrite with bsize in *; omega ].

  - (* polymorphic type *)
    exists (makeFresh ((X :: nil) :: support theta :: pfv T0 type_var :: pfv T4 type_var :: nil)); repeat step || finisher.
    instantiate_any; eapply reduces_to_equiv; eauto 1; steps.
    lazymatch goal with
    | H: reducible_values ((?X,?RC) :: ?theta) ?v _ |- reducible_values ((?M,?RC) :: ?theta) _ _ =>
      apply (reducible_rename_one _ _ _ _ _ M) in H
    end;
      repeat step || finisher || rewrite substitute_topen2.

    t_apply_ih_topen;
      repeat step || autorewrite with bsize in * ||
             apply reducible_unused2 || t_fv_open || t_listutils || apply ite_type_topen ||
             apply left_lex || apply wf_topen || apply fv_nils_topen ||
             finisher || apply is_erased_type_topen;
        try omega;
        eauto with bapply_any;
        eauto with btwf.

  - (* polymorphic type (2) *)
    exists (makeFresh ((X :: nil) :: support theta :: pfv T0 type_var :: pfv T4 type_var :: nil)); repeat step || finisher.
    instantiate_any; eapply reduces_to_equiv; eauto 1; steps.
    lazymatch goal with
    | H: reducible_values ((?X,?RC) :: ?theta) ?v _ |- reducible_values ((?M,?RC) :: ?theta) _ _ =>
      apply (reducible_rename_one _ _ _ _ _ M) in H
    end;
      repeat step || finisher || rewrite substitute_topen2.

    t_apply_ih_topen;
      repeat step || autorewrite with bsize in * ||
             apply reducible_unused2 || t_fv_open || t_listutils || apply ite_type_topen ||
             apply left_lex || apply wf_topen || apply fv_nils_topen ||
             finisher || apply is_erased_type_topen;
        try omega;
        eauto with bapply_any;
        eauto with btwf.

  - unshelve eexists n', v', (makeFresh ((X :: nil) :: pfv T01 type_var
                                                   :: pfv Ts1 type_var
                                                   :: pfv T0 type_var
                                                   :: pfv Ts type_var
                                                   :: support theta :: nil)), _, _; eauto;
      repeat step || finisher;
      try solve [ eapply star_smallstep_ite_inv_true; try eassumption; steps; eauto with values ].

    lazymatch goal with
    | H: reducible_values ((_, _) :: _) _ _ |- reducible_values ((?M,?RC) :: _) _ _ =>
      apply (reducible_rename_one_rc _ RC _ _ _ _ M) in H
    end;
      repeat step || finisher || apply is_erased_type_topen || apply ite_type_topen || t_listutils ||
                rewrite substitute_topen2 || t_apply_ih || t_apply_ih_topen || t_apply_ih_rec ||
                apply wf_topen || apply fv_nils_topen ||
                unfold EquivalentWithRelation.equivalent_rc;
      eauto using reducibility_is_candidate;
      try solve [ apply left_lex; autorewrite with bsize in *; omega ];
      try solve [ apply right_lex; apply lt_index_step; auto ];
      try solve [ constructor; steps ];
      eauto with berased;
      eauto using ite_type_topen;
      eauto with bwf;
      eauto with btwf;
      eauto with bfv.
    + apply right_lex; apply lt_index_step; eauto with values.
      eapply star_smallstep_ite_inv_true; try eassumption; steps; eauto with values.
    + eapply reducible_values_rec_equivalent; eauto; steps; eauto with b_equiv; eauto with berased.
    + apply right_lex; apply lt_index_step; eauto with values.
      eapply star_smallstep_ite_inv_true; try eassumption; steps; eauto with values.

  - unshelve eexists n', v', (makeFresh ((X :: nil) :: pfv T01 type_var
                                                   :: pfv Ts1 type_var
                                                   :: pfv T0 type_var
                                                   :: pfv Ts type_var
                                                   :: support theta :: nil)), _, _; eauto;
      repeat step || finisher || apply star_smallstep_ite_true.

    lazymatch goal with
    | H: reducible_values ((_, _) :: _) _ _ |- reducible_values ((?M,?RC) :: _) _ _ =>
      apply (reducible_rename_one_rc _ RC _ _ _ _ M) in H
    end;
      repeat step || finisher || apply is_erased_type_topen || apply ite_type_topen || t_listutils ||
                rewrite substitute_topen2 || t_apply_ih || t_apply_ih_topen || t_apply_ih_rec ||
                apply wf_topen || apply fv_nils_topen ||
                unfold EquivalentWithRelation.equivalent_rc;
      eauto using reducibility_is_candidate;
      try solve [ apply left_lex; autorewrite with bsize in *; omega ];
      try solve [ apply right_lex; apply lt_index_step; auto ];
      try solve [ constructor; steps ];
      eauto with berased;
      eauto using ite_type_topen;
      eauto with bwf;
      eauto with btwf;
      eauto with bfv.
    eapply reducible_values_rec_equivalent; eauto; steps; eauto with b_equiv; eauto with berased.
Qed.

Lemma reducible_values_T_ite_true:
  forall b T1 T2 T theta v,
    T_ite b T1 T2 T ->
    wf b 0 ->
    wf T1 0 ->
    wf T2 0 ->
    pfv b term_var = nil ->
    pfv T1 term_var = nil ->
    pfv T2 term_var = nil ->
    is_erased_term b ->
    is_erased_type T1 ->
    is_erased_type T2 ->
    star small_step b ttrue ->
    valid_interpretation theta ->
    (reducible_values theta v T <-> reducible_values theta v T1).
Proof.
  eauto using reducible_values_T_ite_true_aux.
Qed.

Ltac t_apply_ih_false :=
  match goal with
  | IH: forall _ _ _ _ _ _, _, H1: T_ite ?b ?T1 ?T2 ?T, H2: reducible_values ?theta ?v ?T2
    |- reducible_values ?theta ?v ?T =>
     is_var T;
     poseNew (Mark T "applying IH");
     unshelve eapply (IH (size T2, index T2) _ b T1 T2 T); eauto
  | IH: forall _ _ _ _ _ _, _, H1: T_ite ?b ?T1 ?T2 ?T, H2: reducible_values ?theta ?v ?T
    |- reducible_values ?theta ?v ?T2 =>
     is_var T;
     poseNew (Mark T "applying IH");
     unshelve eapply (IH (size T2, index T2) _ b T1 T2 T); eauto
  | IH: forall _ _ _ _ _ _, _, H1: T_ite ?b ?T1 ?T2 ?T, H2: reducible_values ?theta ?v (open 0 ?T2 ?a)
    |- reducible_values ?theta ?v (open 0 ?T ?a) =>
     is_var T;
     poseNew (Mark T "applying IH");
     unshelve eapply (IH (size (open 0 T2 a), index (open 0 T2 a)) _ b (open 0 T1 a) (open 0 T2 a) (open 0 T a)); eauto
  | IH: forall _ _ _ _ _ _, _, H1: T_ite ?b ?T1 ?T2 ?T, H2: reducible_values ?theta ?v (open 0 ?T ?a)
    |- reducible_values ?theta ?v (open 0 ?T2 ?a) =>
     is_var T;
     poseNew (Mark T "applying IH");
     unshelve eapply (IH (size (open 0 T2 a), index (open 0 T2 a)) _ b (open 0 T1 a) (open 0 T2 a) (open 0 T a)); eauto
  | IH: forall _ _ _ _ _ _, _, H1: T_ite ?b ?T1 ?T2 ?T, H2: forall a, _ -> _ -> reducible_values ?theta ?v (open 0 ?T2 a)
    |- reducible_values ?theta ?v (open 0 ?T ?a) =>
     is_var T;
     poseNew (Mark T "applying IH");
     unshelve eapply (IH (size (open 0 T2 a), index (open 0 T2 a)) _ b (open 0 T1 a) (open 0 T2 a) (open 0 T a)); eauto
  | IH: forall _ _ _ _ _ _, _, H1: T_ite ?b ?T1 ?T2 ?T, H2: forall a, _ -> _ -> reducible_values ?theta ?v (open 0 ?T a)
    |- reducible_values ?theta ?v (open 0 ?T2 ?a) =>
     is_var T;
     poseNew (Mark T "applying IH");
     unshelve eapply (IH (size (open 0 T2 a), index (open 0 T2 a)) _ b (open 0 T1 a) (open 0 T2 a) (open 0 T a)); eauto
  end.

Ltac t_apply_ih_topen_false :=
  lazymatch goal with
  | IH: forall _ _ _ _ _ _, _, H1: T_ite ?b ?T1 ?T2 ?T, H2: reducible_values ?theta ?v (topen 0 ?T2 ?X)
    |- reducible_values ?theta ?v (topen 0 ?T ?X) =>
     unshelve eapply (IH (size (topen 0 T2 X), index (topen 0 T2 X)) _ b (topen 0 T1 X) (topen 0 T2 X) (topen 0 T X)); eauto
  | IH: forall _ _ _ _ _ _, _, H1: T_ite ?b ?T1 ?T2 ?T, H2: reducible_values ?theta ?v (topen 0 ?T ?X)
    |- reducible_values ?theta ?v (topen 0 ?T2 ?X) =>
     unshelve eapply (IH (size (topen 0 T2 X), index (topen 0 T2 X)) _ b (topen 0 T1 X) (topen 0 T2 X) (topen 0 T X)); eauto
  end.

Ltac t_apply_ih_rec_false :=
  lazymatch goal with
  | IH: forall _ _ _ _ _ _, _, H1: T_ite ?b ?T0' ?T0'' ?T0, H2: T_ite ?b ?Ts' ?Ts'' ?Ts, H3: reducible_values ?theta ?v (T_rec ?n ?T0 ?Ts)
    |- reducible_values ?theta ?v (T_rec ?n ?T0'' ?Ts'') =>
     unshelve eapply (IH (size (T_rec n T0'' Ts''), index (T_rec n T0'' Ts'')) _ b
                         (T_rec n T0' Ts') (T_rec n T0'' Ts'') (T_rec (ite b n n) T0 Ts)); eauto
  | IH: forall _ _ _ _ _ _, _, H1: T_ite ?b ?T0' ?T0'' ?T0, H2: T_ite ?b ?Ts' ?Ts'' ?Ts, H3: reducible_values ?theta ?v (T_rec ?n ?T0'' ?Ts'')
    |- reducible_values ?theta ?v (T_rec ?n ?T0 ?Ts) =>
     apply reducible_values_rec_equivalent with (ite b n n); eauto with b_equiv; steps; eauto with berased;
     unshelve eapply (IH (size (T_rec n T0'' Ts''), index (T_rec n T0'' Ts'')) _ b
                         (T_rec n T0' Ts') (T_rec n T0'' Ts'') (T_rec (ite b n n) T0 Ts)); eauto
  end.

Lemma reducible_values_T_ite_false_aux:
  forall measure b T1 T2 T theta v,
    (size T2, index T2) = measure ->
    T_ite b T1 T2 T ->
    wf b 0 ->
    wf T1 0 ->
    wf T2 0 ->
    pfv b term_var = nil ->
    pfv T1 term_var = nil ->
    pfv T2 term_var = nil ->
    is_erased_term b ->
    is_erased_type T1 ->
    is_erased_type T2 ->
    star small_step b tfalse ->
    valid_interpretation theta ->
    (reducible_values theta v T <-> reducible_values theta v T2).
Proof.
  induction measure using measure_induction; intros; try omega.
  inversion H1;
    repeat match goal with
           | |- reduces_to _ _ => t_reduces_to_open
           | |- reduces_to _ _ => apply_any
           | H: forall a, _ -> _ -> reducible_values ?theta ?v (open 0 ?B a)
               |- reducible_values ?theta ?v (open 0 ?B ?a) => apply H
           | H1: T_ite _ _ ?A2 ?A, H2: reducible_values _ ?v ?A |- reducible_values _ ?v ?A2 \/ _ => left
           | H1: T_ite _ _ ?A2 ?A, H2: reducible_values _ ?v ?A2 |- reducible_values _ ?v ?A \/ _ => left
           | H1: T_ite _ _ ?A2 ?A, H2: reducible_values _ ?v ?A |- _ \/ reducible_values _ ?v ?A2 => right
           | H1: T_ite _ _ ?A2 ?A, H2: reducible_values _ ?v ?A2 |- _ \/ reducible_values _ ?v ?a => right
           | _ => step || t_apply_ih_false || t_dangerous_rec_choice || find_exists_open ||
                 simp_red || apply wf_open || apply fv_nils_open ||
                 t_invert_ite ||
                 t_listutils ||
                 (progress autorewrite with bsize in *) ||
                 find_smallstep_value2 || find_exists || (rewrite (open_none b) by assumption)
           end;
    t_closer;
    eauto 2 using star_smallstep_ite_true;
    eauto 2 using star_smallstep_ite_false;
    eauto 2 with b_equiv;
    eauto 2 with bwf step_tactic;
    try omega;
    eauto using ite_type_open;
    eauto with bwf bfv berased;
    try solve [ apply left_lex; autorewrite with bsize in *; omega ].

  - (* polymorphic type *)
    exists (makeFresh ((X :: nil) :: support theta :: pfv T3 type_var :: pfv T4 type_var :: nil)); repeat step || finisher.
    instantiate_any; eapply reduces_to_equiv; eauto 1; steps.
    lazymatch goal with
    | H: reducible_values ((?X,?RC) :: ?theta) ?v _ |- reducible_values ((?M,?RC) :: ?theta) _ _ =>
      apply (reducible_rename_one _ _ _ _ _ M) in H
    end;
      repeat step || finisher || rewrite substitute_topen2.

    t_apply_ih_topen_false;
      repeat step || autorewrite with bsize in * ||
             apply reducible_unused2 || t_fv_open || t_listutils || apply ite_type_topen ||
             apply left_lex || apply wf_topen || apply fv_nils_topen ||
             finisher || apply is_erased_type_topen;
        try omega;
        eauto with bapply_any;
        eauto with btwf.

  - (* polymorphic type (2) *)
    exists (makeFresh ((X :: nil) :: support theta :: pfv T3 type_var :: pfv T4 type_var :: nil)); repeat step || finisher.
    instantiate_any; eapply reduces_to_equiv; eauto 1; steps.
    lazymatch goal with
    | H: reducible_values ((?X,?RC) :: ?theta) ?v _ |- reducible_values ((?M,?RC) :: ?theta) _ _ =>
      apply (reducible_rename_one _ _ _ _ _ M) in H
    end;
      repeat step || finisher || rewrite substitute_topen2.

    t_apply_ih_topen_false;
      repeat step || autorewrite with bsize in * ||
             apply reducible_unused2 || t_fv_open || t_listutils || apply ite_type_topen ||
             apply left_lex || apply wf_topen || apply fv_nils_topen ||
             finisher || apply is_erased_type_topen;
        try omega;
        eauto with bapply_any;
        eauto with btwf.

  - unshelve eexists n', v', (makeFresh ((X :: nil) :: pfv T02 type_var
                                                   :: pfv Ts2 type_var
                                                   :: pfv T0 type_var
                                                   :: pfv Ts type_var
                                                   :: support theta :: nil)), _, _; eauto;
      repeat step || finisher;
      try solve [ eapply star_smallstep_ite_inv_false; try eassumption; steps; eauto with values ].

    lazymatch goal with
    | H: reducible_values ((_, _) :: _) _ _ |- reducible_values ((?M,?RC) :: _) _ _ =>
      apply (reducible_rename_one_rc _ RC _ _ _ _ M) in H
    end;
      repeat step || finisher || apply is_erased_type_topen || apply ite_type_topen || t_listutils ||
                rewrite substitute_topen2 || t_apply_ih || t_apply_ih_topen_false || t_apply_ih_rec_false ||
                apply wf_topen || apply fv_nils_topen ||
                unfold EquivalentWithRelation.equivalent_rc;
      eauto using reducibility_is_candidate;
      try solve [ apply left_lex; autorewrite with bsize in *; omega ];
      try solve [ apply right_lex; apply lt_index_step; auto ];
      try solve [ constructor; steps ];
      eauto with berased;
      eauto using ite_type_topen;
      eauto with bwf;
      eauto with btwf;
      eauto with bfv.
    + apply right_lex; apply lt_index_step; eauto with values.
      eapply star_smallstep_ite_inv_false; try eassumption; steps; eauto with values.
    + eapply reducible_values_rec_equivalent; eauto; steps; eauto with b_equiv; eauto with berased.
    + apply right_lex; apply lt_index_step; eauto with values.
      eapply star_smallstep_ite_inv_false; try eassumption; steps; eauto with values.

  - unshelve eexists n', v', (makeFresh ((X :: nil) :: pfv T02 type_var
                                                   :: pfv Ts2 type_var
                                                   :: pfv T0 type_var
                                                   :: pfv Ts type_var
                                                   :: support theta :: nil)), _, _; eauto;
      repeat step || finisher || apply star_smallstep_ite_false.

    lazymatch goal with
    | H: reducible_values ((_, _) :: _) _ _ |- reducible_values ((?M,?RC) :: _) _ _ =>
      apply (reducible_rename_one_rc _ RC _ _ _ _ M) in H
    end;
      repeat step || finisher || apply is_erased_type_topen || apply ite_type_topen || t_listutils ||
                rewrite substitute_topen2 || t_apply_ih || t_apply_ih_topen_false || t_apply_ih_rec_false ||
                apply wf_topen || apply fv_nils_topen ||
                unfold EquivalentWithRelation.equivalent_rc;
      eauto using reducibility_is_candidate;
      try solve [ apply left_lex; autorewrite with bsize in *; omega ];
      try solve [ apply right_lex; apply lt_index_step; auto ];
      try solve [ constructor; steps ];
      eauto with berased;
      eauto using ite_type_topen;
      eauto with bwf;
      eauto with btwf;
      eauto with bfv.
    eapply reducible_values_rec_equivalent; eauto; steps; eauto with b_equiv; eauto with berased.
Qed.

Lemma reducible_values_T_ite_false:
  forall b T1 T2 T theta v,
    T_ite b T1 T2 T ->
    wf b 0 ->
    wf T1 0 ->
    wf T2 0 ->
    pfv b term_var = nil ->
    pfv T1 term_var = nil ->
    pfv T2 term_var = nil ->
    is_erased_term b ->
    is_erased_type T1 ->
    is_erased_type T2 ->
    star small_step b tfalse ->
    valid_interpretation theta ->
    (reducible_values theta v T <-> reducible_values theta v T2).
Proof.
  eauto using reducible_values_T_ite_false_aux.
Qed.

Lemma reducible_T_ite:
  forall theta T1 T2 T b t1 t2,
    wf t1 0 ->
    wf t2 0 ->
    wf T1 0 ->
    wf T2 0 ->
    pfv t1 term_var = nil ->
    pfv t2 term_var = nil ->
    pfv T1 term_var = nil ->
    pfv T2 term_var = nil ->
    is_erased_term t1 ->
    is_erased_term t2 ->
    is_erased_type T1 ->
    is_erased_type T2 ->
    valid_interpretation theta ->
    reducible theta b T_bool ->
    T_ite b T1 T2 T ->
    (equivalent b ttrue -> reducible theta t1 T1) ->
    (equivalent b tfalse -> reducible theta t2 T2) ->
    reducible theta (ite b t1 t2) T.
Proof.
  intros.
  match goal with
  | H: reducible _ _ T_bool |- _ =>
    unfold reducible, reduces_to, closed_term in H
  end; repeat step || simp reducible_values in *.

  - apply star_backstep_reducible with (ite ttrue t1 t2); repeat step || t_listutils;
      auto with bsteplemmas; eauto with bfv; eauto with bwf.
    eapply backstep_reducible; repeat step || t_listutils;
      eauto 2 with smallstep;
      eauto with bfv;
      eauto with bwf;
      eauto with b_equiv.
    apply reducible_values_exprs with T1; steps; eauto with b_equiv.
    eapply reducible_values_T_ite_true; eauto; steps.
  - apply star_backstep_reducible with (ite tfalse t1 t2); repeat step || t_listutils;
      auto with bsteplemmas; eauto with bfv; eauto with bwf.
    eapply backstep_reducible; repeat step || t_listutils;
      eauto 2 with smallstep;
      eauto with bfv;
      eauto with bwf;
      eauto with b_equiv.
    apply reducible_values_exprs with T2; steps; eauto with b_equiv.
    eapply reducible_values_T_ite_false; eauto; steps.
Qed.

Lemma open_reducible_T_ite:
  forall tvars gamma T T1 T2 b t1 t2 x,
    wf t1 0 ->
    wf t2 0 ->
    wf T1 0 ->
    wf T2 0 ->
    is_erased_term t1 ->
    is_erased_term t2 ->
    is_erased_type T1 ->
    is_erased_type T2 ->
    subset (fv t1) (support gamma) ->
    subset (fv t2) (support gamma) ->
    subset (fv T1) (support gamma) ->
    subset (fv T2) (support gamma) ->
    ~(x ∈ fv b) ->
    ~(x ∈ fv t1) ->
    ~(x ∈ fv t2) ->
    ~(x ∈ fv T1) ->
    ~(x ∈ fv T2) ->
    ~(x ∈ fv_context gamma) ->
    ~(x ∈ tvars) ->
    is_erased_term b ->
    is_erased_term t1 ->
    is_erased_term t2 ->
    T_ite b T1 T2 T ->
    open_reducible tvars gamma b T_bool ->
    open_reducible tvars ((x, T_equal b ttrue) :: gamma) t1 T1 ->
    open_reducible tvars ((x, T_equal b tfalse) :: gamma) t2 T2 ->
    open_reducible tvars gamma (ite b t1 t2) T.
Proof.
  intros; unfold open_reducible; steps.

  unfold open_reducible in *.
  apply reducible_T_ite with (substitute T1 lterms) (substitute T2 lterms);
    repeat step || t_termlist || apply ite_type_subst;
    eauto with bwf;
    eauto using subset_same with bfv;
    eauto with berased.
  - unshelve epose proof (H23 _ ((x, uu) :: lterms) _ _ _); tac1.
  - unshelve epose proof (H24 _ ((x, uu) :: lterms) _ _ _); tac1.
Qed.
