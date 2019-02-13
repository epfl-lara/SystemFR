Require Import Equations.Equations.
Require Import Equations.Subterm.

Require Import Omega.

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import Termination.StarInversions.
Require Import Termination.StarRelation.
Require Import Termination.SmallStep.
Require Import Termination.Syntax.
Require Import Termination.Trees.
Require Import Termination.Tactics.
Require Import Termination.Equivalence.
Require Import Termination.OpenTOpen.

Require Import Termination.SizeLemmas.

Require Import Termination.WFLemmas.
Require Import Termination.TWFLemmas.
Require Import Termination.ErasedTermLemmas.

Require Import Termination.ReducibilityCandidate.
Require Import Termination.ReducibilityDefinition.
Require Import Termination.ReducibilityLemmas.
Require Import Termination.RedTactics.
Require Import Termination.ReducibilityMeasure.
Require Import Termination.ReducibilitySubst.
Require Import Termination.ReducibilityRenaming.
Require Import Termination.ReducibilityUnused.
Require Import Termination.RedTactics2.

Require Import Termination.IdRelation.
Require Import Termination.EqualWithRelation.

Require Import Termination.EquivalentWithRelation.
Require Import Termination.AssocList.
Require Import Termination.Sets.
Require Import Termination.Freshness.
Require Import Termination.SwapHoles.
Require Import Termination.ListUtils.
Require Import Termination.TOpenTClose.
Require Import Termination.StrictPositivity.
Require Import Termination.NoTypeFVar.

Require Import Termination.FVLemmas.

Opaque makeFresh.
Opaque Nat.eq_dec.
Opaque reducible_values.
Opaque strictly_positive.

Definition pre_interpretation := list (nat * (tree -> tree -> Prop)).

Fixpoint forall_implicate (P: tree -> Prop) (pre_theta: pre_interpretation) (theta: interpretation) :=
  match pre_theta, theta with
  | nil, nil => True
  | (X,pre_rc) :: pre_theta', (Y,rc) :: theta' =>
      X = Y /\
      forall_implicate P pre_theta' theta' /\
      forall (v: tree), (forall a, P a -> pre_rc a v) -> rc v
  | _, _ => False
  end.

Lemma forall_implicate_apply:
  forall P pre_theta theta X pre_rc rc v,
    forall_implicate P pre_theta theta ->
    lookup Nat.eq_dec pre_theta X = Some pre_rc ->
    lookup Nat.eq_dec theta X = Some rc ->
    (forall a, P a -> pre_rc a v) ->
    rc v.
Proof.
  induction pre_theta; destruct theta; repeat step || eapply_any.
Qed.

Ltac t_forall_implicate_apply :=
  match goal with
  | H1: forall_implicate ?P ?ptheta ?theta,
    H2: lookup _ ?ptheta ?X = Some ?prc,
    H3: lookup _ ?theta ?X = Some ?rc |- ?rc ?v =>
    apply (forall_implicate_apply _ _ _ _ _ _ _ H1 H2 H3)
  end.

Lemma forall_implicate_support:
  forall P pre_theta theta,
    forall_implicate P pre_theta theta ->
    support pre_theta = support theta.
Proof.
  induction pre_theta; destruct theta; repeat step || f_equal.
Qed.

Ltac t_forall_implicate_support :=
  match goal with
  | H: forall_implicate ?P ?ptheta ?theta |- _ =>
    poseNew (Mark (ptheta,theta) "forall_implicate_suppoft");
    pose proof (forall_implicate_support _ _ _ H)
  end.

Lemma strictly_positive_push_forall_fvar:
  forall (n : nat) theta theta' (pre_theta : list (nat * (tree -> tree -> Prop))) X (A : tree) v,
    non_empty theta A ->
    (forall a : tree,
        reducible_values theta a A ->
        reducible_values (push_one a pre_theta ++ theta) v (fvar X type_var)) ->
    forall_implicate (fun a => reducible_values theta a A) pre_theta theta' ->
    reducible_values (theta' ++ theta) v (fvar X type_var).
Proof.
  unfold push_all, push_one;
  intros; t_instantiate_non_empty;
    repeat match goal with
           | _ => step || simp_red || t_instantiate_reducible || rewrite support_mapValues in * || t_listutils
           | _ => t_lookup_same || t_lookupor || t_lookup_rewrite || t_lookupMap2 || t_lookup
           | _ => t_forall_implicate_apply || t_forall_implicate_support
           end.
Qed.

Hint Resolve strictly_positive_push_forall_fvar: b_push.

Lemma reducible_unused_many1:
  forall theta' theta T v,
    no_type_fvar T (support theta') ->
    valid_interpretation theta ->
    valid_interpretation theta' ->
    reducible_values (theta' ++ theta) v T ->
    reducible_values theta v T.
Proof.
  induction theta';
    repeat step || (poseNew (Mark 0 "once"); eapply IHtheta') || t_reducible_unused3 ||
           apply valid_interpretation_append || apply valid_interpretation_all || unfold sat in * ||
           unfold reducibility_candidate in * || instantiate_any;
    eauto with b_no_type_fvar.
Qed.

Lemma reducible_unused_many2:
  forall theta' theta T v,
    no_type_fvar T (support theta') ->
    valid_interpretation theta ->
    valid_interpretation theta' ->
    reducible_values theta v T ->
    reducible_values (theta' ++ theta) v T.
Proof.
  induction theta';
    repeat step || (poseNew (Mark 0 "once"); eapply IHtheta') || apply reducible_unused2 ||
           apply valid_interpretation_append || apply valid_interpretation_all || unfold sat in * ||
           unfold reducibility_candidate in * || instantiate_any;
    eauto with b_no_type_fvar.
Qed.

Lemma reducible_unused_many:
  forall theta' theta T v,
    no_type_fvar T (support theta') ->
    valid_interpretation theta ->
    valid_interpretation theta' -> (
      reducible_values (theta' ++ theta) v T <->
      reducible_values theta v T
    ).
Proof.
  intuition auto; eauto using reducible_unused_many1, reducible_unused_many2.
Qed.

Ltac t_instantiate_reducible2 :=
  match goal with
  | H0: no_type_fvar ?T (support ?theta'),
    H1:reducible_values _ ?v ?T,
    H2:is_erased_term ?v,
    H3: forall a, _ -> reducible_values (push_one _ ?ptheta ++ ?theta) a ?T -> _,
    H4: forall_implicate _ ?ptheta ?theta'
    |- _ => poseNew (Mark (v, H3) "t_instantiate_reducible2");
          unshelve epose proof (H3 v H2 _)
  end.

Ltac success t := (t; fail) || (t; []).

Ltac t_rewrite_support :=
  match goal with
  | H: support _ = support _ |- _ => rewrite H in *
  end.

Ltac t_rewriter :=
  repeat step || t_listutils || unfold no_type_fvar in * || t_forall_implicate_support ||
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
  | H1: non_empty ?theta ?A,
    H2: forall_implicate _ ?ptheta ?theta' |- reducible_values (?theta' ++ _) _ ?T =>
      apply H with (size T, index T) ptheta A
  end.

Lemma strictly_positive_push_forall:
  forall measure T pre_theta theta theta' A v,
    (size T, index T) = measure ->
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
    forall_implicate (fun a => reducible_values theta a A) pre_theta theta' ->
    reducible_values (theta' ++ theta) v T.
Proof.
  induction measure as [ PP HH ] using measure_induction; intros; t_instantiate_non_empty;
    destruct T; try destruct_tag;
    eauto with b_push;
    repeat match goal with
    | |- closed_term _ => solve [ t_closing; eauto with bfv bwf b_valid_interp ]
    | |- wf _ _ => solve [ t_closing; repeat step || apply wf_open ]
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
      find_exists2 ||
      ( progress autorewrite with bsize in * ) ||
      (rewrite reducible_unused_many in * by t_rewriter) ||
      (rewrite open_topen in * by (steps; eauto with btwf; eauto with bwf)) ||
      (rewrite no_type_lvar_topen in * by (repeat step || apply no_type_lvar_open || apply is_erased_type_open; eauto with btwf)) ||
      apply_induction HH
    end;
    try omega;
    eauto using reducible_values_closed;
    eauto with berased bwf btwf;
    try solve [ apply twf_open; eauto with btwf ];
    eauto with b_red_is_val;
    eauto using no_type_fvar_strictly_positive;
    try solve [ apply_any; assumption ].

  (** Polymorphic type **)
  - exists (makeFresh (
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
        try solve [ apply valid_interpretation_all; eauto using sat_p ];
        try finisher;
        eauto with b_red_is_val.

    apply_induction HH;
      repeat
        step || t_valid_interpretation_equiv || t_forall_implicate_equiv ||
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
    + apply reducible_unused3 in H29; repeat step; try finisher; eauto with bapply_any.
    + apply reducible_unused3 in H29;
        repeat step || t_instantiate_reducible || t_deterministic_star ||
               t_instantiate_rc || simp_red || unfold reduces_to in *;
        try finisher; eauto with bapply_any;
          eauto with b_red_is_val.
      apply reducible_rename_permute with X1; repeat step || rewrite support_push_one in *;
        eauto with b_valid_interp;
        try finisher.
    + apply reducible_unused2; steps; try finisher; eauto with bapply_any.
    + apply reducible_unused3 in H29; steps; try finisher; eauto with bapply_any.

  (** Recursive type at 0: case where the recursive type is itself strictly positive **)
  - left.
      repeat step || simp_red ||
             t_instantiate_reducible || apply_induction HH || apply left_lex ||
             t_deterministic_star ||
             t_topen_none; eauto with omega;
        eauto with bapply_any.

  (** Recursive type at n+1: case where the variables do not appear in the recursive type **)
  - right.
      exists n'0, v'0, (makeFresh (
                       support theta ::
                       support pre_theta ::
                       support theta' ::
                       pfv A type_var ::
                       pfv T2 type_var ::
                       pfv T3 type_var ::
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
          repeat step || t_listutils || t_forall_implicate_support || t_rewrite_support ||
                 apply valid_interpretation_append ||
                 apply valid_interpretation_all ||
                 (eapply valid_interpretation_one; eauto) ||
                 apply no_type_fvar_in_topen ||
                 rewrite support_push_one in * ||
                 rewrite support_push_all in * ||
                 apply reducibility_is_candidate;
          eauto using sat_p;
          try solve [ apply_any; assumption ];
          try finisher
        ).

      eapply reducible_rename_one_rc; eauto;
        repeat step ||
               (rewrite reducible_unused_many in * by t_rewriter) ||
               apply reducibility_is_candidate ||
               unfold equivalent_rc;
        eauto using sat_p with b_valid_interp bapply_any;
        try finisher.

  (** Recursive type at n+1: case where the recursive type is itself strictly positive **)
  - right.
      exists n'0, v'0, (makeFresh (
                       support theta ::
                       support pre_theta ::
                       support theta' ::
                       pfv A type_var ::
                       pfv T2 type_var ::
                       pfv T3 type_var ::
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
        H2: forall_implicate _ ?ptheta ?theta' |-
          reducible_values (((?X, fun t => reducible_values (?theta' ++ ?theta) t ?R) :: ?theta') ++ ?theta) _ ?T =>
          apply HH with (size T, index T) ((X, fun a t => reducible_values (push_one a pre_theta ++ theta) t R) :: ptheta) A
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
      + simp reducible_values in H37;
          repeat step || t_deterministic_star.
        eapply reducible_rename_one; eauto;
          repeat step; eauto using reducibility_is_candidate with b_valid_interp;
            try finisher.
      + (* We apply one last time the induction hypothesis for rec(n) *)
        apply_induction HH;
          repeat step || apply right_lex || simp_spos; eauto using lt_index_step;
            eauto with bwf btwf berased.
Qed.
