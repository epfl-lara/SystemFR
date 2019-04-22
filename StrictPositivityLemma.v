Require Import Equations.Equations.
Require Import Equations.Subterm.

Require Import Omega.

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import SystemFR.StarInversions.
Require Import SystemFR.StarRelation.
Require Import SystemFR.SmallStep.
Require Import SystemFR.Syntax.
Require Import SystemFR.Trees.
Require Import SystemFR.Tactics.
Require Import SystemFR.Equivalence.
Require Import SystemFR.OpenTOpen.

Require Import SystemFR.SizeLemmas.


Require Import SystemFR.WFLemmas.
Require Import SystemFR.TWFLemmas.
Require Import SystemFR.ErasedTermLemmas.

Require Import SystemFR.ReducibilityCandidate.
Require Import SystemFR.ReducibilityDefinition.
Require Import SystemFR.ReducibilityLemmas.
Require Import SystemFR.RedTactics.
Require Import SystemFR.ReducibilityMeasure.
Require Import SystemFR.ReducibilitySubst.
Require Import SystemFR.ReducibilityRenaming.
Require Import SystemFR.ReducibilityUnused.
Require Import SystemFR.RedTactics2.

Require Import SystemFR.IdRelation.
Require Import SystemFR.EqualWithRelation.

Require Import SystemFR.EquivalentWithRelation.
Require Import SystemFR.AssocList.
Require Import SystemFR.Sets.
Require Import SystemFR.Freshness.
Require Import SystemFR.SwapHoles.
Require Import SystemFR.ListUtils.
Require Import SystemFR.TOpenTClose.
Require Import SystemFR.StrictPositivity.
Require Import SystemFR.StrictPositivityLemmas.
Require Import SystemFR.NoTypeFVar.

Require Import SystemFR.FVLemmas.

Opaque makeFresh.
Opaque Nat.eq_dec.
Opaque reducible_values.
Opaque strictly_positive.

Ltac t_instantiate_reducible2 :=
  match goal with
  | H0: no_type_fvar ?T (support ?theta'),
    H1: reducible_values _ ?v ?T,
    H2: is_erased_term ?v,
    H3: forall a, _ -> reducible_values (push_one _ ?ptheta ++ ?theta) a ?T -> _,
    H4: forall_implies _ ?ptheta ?theta'
    |- _ => poseNew (Mark (v, H3) "t_instantiate_reducible2");
          unshelve epose proof (H3 v H2 _)
  end.

Ltac t_rewrite_support :=
  match goal with
  | H: support _ = support _ |- _ => rewrite H in *
  end.

Ltac t_rewriter :=
  repeat step || t_listutils || unfold no_type_fvar in * || t_forall_implies_support ||
         t_fv_open ||
         (rewrite is_erased_term_tfv in * by (steps; eauto with berased)) ||
         rewrite support_push_all in * || rewrite support_push_one in *;
    eauto with bapply_any;
    eauto with b_valid_interp;
    eauto 2 with beapply_any step_tactic;
    try solve [ eapply_any; eauto; steps ];
    try finisher.

Ltac apply_induction H :=
  match goal with
    H2: forall_implies (fun _ => reducible_values _ _ ?A) ?ptheta ?theta' |-
      reducible_values (?theta' ++ _) _ ?T =>
      apply H with (size T, index T) ptheta A
  end.

Ltac find_exists3 :=
  match goal with
  | H: reducible_values _ ?v ?T
    |- exists x, reducible_values _ x ?T =>
    exists v
  end.

Definition sp_push_forall_prop T: Prop :=
  forall pre_theta theta theta' A v,
    wf T 0 ->
    twf T 0 ->
    wf A 0 ->
    twf A 0 ->
    valid_interpretation theta ->
    valid_interpretation theta' ->
    non_empty theta A ->
    valid_pre_interpretation (fun a => reducible_values theta a A) pre_theta ->
    strictly_positive T (support theta') ->
    is_erased_type A ->
    is_erased_type T ->
    (forall a,
      reducible_values theta a A ->
      reducible_values (push_one a pre_theta ++ theta) v T) ->
    forall_implies (fun a => reducible_values theta a A) pre_theta theta' ->
    reducible_values (theta' ++ theta) v T.

Definition sp_push_forall_prop_aux m T: Prop := (size T, index T) = m -> sp_push_forall_prop T.

Definition sp_push_forall_until m: Prop := forall m', m' << m -> forall T', sp_push_forall_prop_aux m' T'.

Hint Unfold sp_push_forall_prop: u_push.
Hint Unfold sp_push_forall_until: u_push.
Hint Unfold sp_push_forall_prop_aux: u_push.

Lemma sp_push_forall_fvar: forall m n f, sp_push_forall_prop_aux m (fvar n f).
Proof.
  autounfold with u_push;
  unfold push_all, push_one;
  intros; t_instantiate_non_empty;
    repeat match goal with
           | _ => step || simp_red || t_instantiate_reducible || rewrite support_mapValues in * || t_listutils
           | _ => t_lookup_same || t_lookupor || t_lookup_rewrite || t_lookupMap2 || t_lookup
           | _ => t_forall_implies_apply || t_forall_implies_support
           end.
Qed.

Hint Immediate sp_push_forall_fvar: b_push.

Ltac t_spos_proof HH :=
      repeat match goal with
    | |- closed_term _ => solve [ t_closing; eauto with bfv bwf b_valid_interp ]
    | |- wf _ _ => solve [ t_closing; repeat step || apply wf_open ]
    | H: star small_step _ zero |- _ \/ _ => left
    | |- exists x, tfold ?v = tfold x /\ _ => unshelve exists v
    | _ =>
      step ||
      simp_red ||
      simp_spos ||
      t_topen_none ||
      t_instantiate_reducible ||
      t_instantiate_reducible2 ||
      find_reducible_value ||
      reducibility_choice ||
      t_deterministic_star ||
      ( progress unfold reduces_to in * ) ||
      find_smallstep_value ||
      apply strictly_positive_open ||
      apply left_lex ||
      find_exists ||
      find_exists3 ||
      find_exists2 || (* must be after find_exists3 *)
      ( progress autorewrite with bsize in * ) ||
      (rewrite reducible_unused_many in * by t_rewriter) ||
      (rewrite open_topen in * by (steps; eauto with btwf; eauto with bwf)) ||
      apply_induction HH
    end;
    try omega;
    eauto using reducible_values_closed;
    eauto with berased bwf btwf;
    try solve [ apply twf_open; eauto with btwf ];
    eauto with b_red_is_val;
    eauto using no_type_fvar_strictly_positive;
    try solve [ apply_any; assumption ];
    eauto with btwf2.

Lemma sp_push_forall_arrow:
  forall m T1 T2, sp_push_forall_until m -> sp_push_forall_prop_aux m (T_arrow T1 T2).
Proof.
  repeat autounfold with u_push; intros; t_instantiate_non_empty;
    repeat step || simp_red || simp_spos.
  t_spos_proof H.
Qed.

Hint Immediate sp_push_forall_arrow: b_push.

Lemma sp_push_forall_prod:
  forall m T1 T2, sp_push_forall_until m -> sp_push_forall_prop_aux m (T_prod T1 T2).
Proof.
  repeat autounfold with u_push; intros; t_instantiate_non_empty;
    repeat step || simp_red || simp_spos.
  t_spos_proof H.
Qed.

Hint Immediate sp_push_forall_prod: b_push.

Lemma sp_push_forall_sum:
  forall m T1 T2, sp_push_forall_until m -> sp_push_forall_prop_aux m (T_sum T1 T2).
Proof.
  repeat autounfold with u_push; intros; t_instantiate_non_empty;
    repeat step || simp_red || simp_spos.
  - find_exists; t_spos_proof H.
  - find_exists; t_spos_proof H.
Qed.

Hint Immediate sp_push_forall_sum: b_push.

Lemma sp_push_forall_refine:
  forall m T b, sp_push_forall_until m -> sp_push_forall_prop_aux m (T_refine T b).
Proof.
  repeat autounfold with u_push; intros; t_instantiate_non_empty;
    repeat step || simp_red || simp_spos.
  t_spos_proof H.
Qed.

Hint Immediate sp_push_forall_refine: b_push.

Lemma sp_push_forall_type_refine:
  forall m T1 T2, sp_push_forall_until m -> sp_push_forall_prop_aux m (T_type_refine T1 T2).
Proof.
  repeat autounfold with u_push; intros; t_instantiate_non_empty;
    repeat step || simp_red || simp_spos.
  - t_spos_proof H.
  - t_spos_proof H.
Qed.

Hint Immediate sp_push_forall_type_refine: b_push.

Lemma sp_push_forall_let:
  forall m t T, sp_push_forall_until m -> sp_push_forall_prop_aux m (T_let t T).
Proof.
  repeat autounfold with u_push; intros; t_instantiate_non_empty;
    repeat step || simp_red || simp_spos.
  t_spos_proof H.
Qed.

Hint Immediate sp_push_forall_let: b_push.

Lemma sp_push_forall_intersection:
  forall m T1 T2, sp_push_forall_until m -> sp_push_forall_prop_aux m (T_intersection T1 T2).
Proof.
  repeat autounfold with u_push; intros; t_instantiate_non_empty;
    repeat step || simp_red || simp_spos.
  - t_spos_proof H.
  - t_spos_proof H.
Qed.

Hint Immediate sp_push_forall_intersection: b_push.

Lemma sp_push_forall_union:
  forall m T1 T2, sp_push_forall_until m -> sp_push_forall_prop_aux m (T_union T1 T2).
Proof.
  repeat autounfold with u_push; intros; t_instantiate_non_empty;
    repeat step || simp_red || simp_spos.
  - t_spos_proof H.
  - t_spos_proof H.
Qed.

Hint Immediate sp_push_forall_union: b_push.

Lemma sp_push_forall_forall:
  forall m T1 T2, sp_push_forall_until m -> sp_push_forall_prop_aux m (T_forall T1 T2).
Proof.
  repeat autounfold with u_push; intros; t_instantiate_non_empty;
    repeat step || simp_red || simp_spos.
  t_spos_proof H.
Qed.

Hint Immediate sp_push_forall_forall: b_push.

Lemma sp_push_forall_exists:
  forall m T1 T2, sp_push_forall_until m -> sp_push_forall_prop_aux m (T_exists T1 T2).
Proof.
  repeat autounfold with u_push; intros; t_instantiate_non_empty;
    repeat step || simp_red || simp_spos.
  t_spos_proof H.
Qed.

Hint Immediate sp_push_forall_exists: b_push.

Lemma sp_push_forall_abs:
  forall m T, sp_push_forall_until m -> sp_push_forall_prop_aux m (T_abs T).
Proof.
  repeat autounfold with u_push; intros; t_instantiate_non_empty;
    repeat step || simp_red || simp_spos.
  t_spos_proof H.

  exists (makeFresh (
         support theta ::
         support pre_theta ::
         support theta' ::
         pfv A type_var ::
         pfv T type_var ::
         nil));
    repeat step || finisher || t_instantiate_rc || find_smallstep_value || t_listutils;
      try solve [ repeat unfold closed_term, closed_value in * || step ].

  lazymatch goal with
  | |- reducible_values ((?X,?RC) :: ?g1 ++ ?g2) _ (topen 0 ?T ?rep) =>
    apply reducible_rename with (topen 0 T rep) (g1 ++ (X,RC) :: g2)
                                (idrel (X :: support g1 ++ support g2 ++ pfv T type_var))
  end;
    repeat step || apply valid_interpretation_append || t_deterministic_star ||
           apply push_all_is_candidate || apply equivalent_with_relation_permute ||
           apply equal_with_relation_refl2 ||
           rewrite idrel_lookup || t_fv_open ||
           rewrite idrel_lookup_swap || t_fv_open ||
           t_listutils;
      eauto with b_valid_interp;
      eauto using reducibility_is_candidate;
      try solve [ unfold equivalent_rc; steps; eauto ];
      try finisher;
      eauto with b_red_is_val.

  apply_induction H;
    repeat
      step || t_valid_interpretation_equiv || t_forall_implies_equiv ||
      apply left_lex ||
      (progress autorewrite with bsize in * ) ||
      apply strictly_positive_swap ||
      apply twf_topen ||
      apply is_erased_type_topen ||
      apply non_empty_extend ||
      t_deterministic_star ||
      apply strictly_positive_topen ||
      apply wf_topen;
    try finisher;
    eauto with bwf btwf omega berased;
    eauto 2 using red_is_val with step_tactic;
    eauto with b_red_is_val;
    try solve [ apply_any; assumption ].

  + apply reducible_unused2; steps; try finisher; eauto with bapply_any.
  + apply reducible_unused3 in H30; repeat step; try finisher; eauto with bapply_any.
  + apply reducible_unused3 in H30;
      repeat step || t_instantiate_reducible || t_deterministic_star ||
             t_instantiate_rc || simp_red || unfold reduces_to in *;
      try finisher; eauto with bapply_any;
        eauto with b_red_is_val.
    apply reducible_rename_permute with X1; repeat step || rewrite support_push_one in *;
      eauto with b_valid_interp;
      try finisher.
  + apply reducible_unused2; steps; try finisher; eauto with bapply_any.
  + apply reducible_unused3 in H30; steps; try finisher; eauto with bapply_any.
Qed.

Hint Immediate sp_push_forall_abs: b_push.

Lemma sp_push_forall_rec:
  forall m n T0 Ts, sp_push_forall_until m -> sp_push_forall_prop_aux m (T_rec n T0 Ts).
Proof.
  repeat autounfold with u_push; intros; t_instantiate_non_empty;
    t_spos_proof H.

  (** Recursive type at n+1: case where the variables do not appear in the recursive type **)
  - right.
      exists n'0, v'0, (makeFresh (
                       support theta ::
                       support pre_theta ::
                       support theta' ::
                       pfv A type_var ::
                       pfv T0 type_var ::
                       pfv Ts type_var ::
                       pfv n'0 type_var ::
                       nil));
      repeat step || simp_red || t_listutils ||
             t_instantiate_reducible ||
             t_deterministic_star ||
             t_topen_none;
        eauto with omega;
        try finisher.

      repeat
        rewrite reducible_unused_middle in * by (
          repeat step || t_listutils || t_forall_implies_support || t_rewrite_support ||
                 apply valid_interpretation_append ||
                 (eapply valid_interpretation_one; eauto) ||
                 apply no_type_fvar_in_topen ||
                 rewrite support_push_one in * ||
                 rewrite support_push_all in * ||
                 apply reducibility_is_candidate;
          try solve [ apply_any; assumption ];
          try finisher
        ).

      eapply reducible_rename_one_rc; eauto;
        repeat step ||
               (rewrite reducible_unused_many in * by t_rewriter) ||
               apply reducibility_is_candidate ||
               unfold equivalent_rc;
        eauto with b_valid_interp bapply_any;
        try finisher.

  (** Recursive type at n+1: case where the recursive type is itself strictly positive **)
  - right.
      exists n'0, v'0, (makeFresh (
                       support theta ::
                       support pre_theta ::
                       support theta' ::
                       pfv A type_var ::
                       pfv T0 type_var ::
                       pfv Ts type_var ::
                       pfv n'0 type_var ::
                       nil));
      repeat step || simp_red || t_listutils ||
             t_instantiate_reducible ||
             t_deterministic_star ||
             t_topen_none;
        eauto with omega;
        try finisher.

      rewrite app_comm_cons.
      lazymatch goal with
      | H1: non_empty ?theta ?A,
        H2: forall_implies _ ?ptheta ?theta' |-
          reducible_values (((?X, fun t => reducible_values (?theta' ++ ?theta) t ?R) :: ?theta') ++ ?theta) _ ?T =>
          apply H with (size T, index T) ((X, fun a t => reducible_values (push_one a pre_theta ++ theta) t R) :: ptheta) A
      end;
        repeat
          step || apply left_lex || autorewrite with bsize in * || t_deterministic_star ||
          apply is_erased_type_topen || t_instantiate_reducible ||
          apply wf_topen || apply twf_topen || apply reducibility_is_candidate ||
          (poseNew (Mark 0 "strictly_positive_topen2"); apply strictly_positive_topen2);
        try omega;
        eauto with b_valid_interp;
        try finisher.

      + eapply strictly_positive_rename_one; eauto;
          repeat step;
          try finisher.
      + simp reducible_values in H38;
          repeat step || t_deterministic_star.
        eapply reducible_rename_one; eauto;
          repeat step; eauto using reducibility_is_candidate with b_valid_interp;
            try finisher.
      + (* We apply one last time the induction hypothesis for rec(n) *)
        apply_induction H;
          repeat step || apply right_lex || simp_spos; eauto using lt_index_step;
            eauto with bwf btwf berased.
Qed.

Hint Immediate sp_push_forall_rec: b_push.

Lemma strictly_positive_push_forall_aux: forall m T, sp_push_forall_prop_aux m T.
Proof.
  induction m using measure_induction; destruct T;
    eauto 2 with b_push;
    try solve [ autounfold with u_push; intros; t_instantiate_non_empty; repeat step || simp_red ].
Qed.

Lemma strictly_positive_push_forall: forall T, sp_push_forall_prop T.
Proof.
  intros.
  eapply strictly_positive_push_forall_aux; eauto 1.
Qed.
