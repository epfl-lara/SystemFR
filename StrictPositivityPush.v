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

Require Import Termination.FVLemmas.

Opaque makeFresh.
Opaque Nat.eq_dec.
Opaque reducible_values.
Opaque strictly_positive.

Lemma strictly_positive_push_forall_fvar:
  forall (n : nat) (theta : interpretation) (theta' : list (nat * (tree -> tree -> Prop))) X (A : tree) v P,
    non_empty theta A ->
    (forall a : tree,
        reducible_values theta a A ->
        reducible_values (push_one a theta' ++ theta) v (fvar X type_var)) ->
    (forall a, P a <-> reducible_values theta a A) ->
    reducible_values (push_all P theta' ++ theta) v (fvar X type_var).
Proof.
  unfold push_all, push_one;
  intros; t_instantiate_non_empty;
    repeat match goal with
           | H1: forall a, ?P a <-> reducible_values ?theta a ?A, H2: ?P ?a |- _ =>
              poseNew (Mark H2 "equiv_inst");
              pose proof (proj1 (H1 a) H2)
           | _ =>
             t_lookup_same || step || simp_red || t_lookupor || t_lookup_rewrite || t_lookupMap2 || t_instantiate_reducible || t_lookup || rewrite support_mapValues in * || t_listutils
           end.
Qed.

Hint Resolve strictly_positive_push_forall_fvar: b_push.

Ltac apply_induction H :=
  match goal with
  | H1: non_empty ?theta ?A |- reducible_values (push_all _ _ ++ _) _ ?T =>
      apply H with (size T, index T) A
  end.

Lemma strictly_positive_push_forall:
  forall measure T theta theta' A v P,
    (size T, index T) = measure ->
    wf T 0 ->
    twf T 0 ->
    wf A 0 ->
    twf A 0 ->
    valid_interpretation theta ->
    non_empty theta A ->
    valid_pre_interpretation P theta' ->
    strictly_positive T (support theta') ->
    is_erased_type A ->
    is_erased_type T ->
    (forall a,
      reducible_values theta a A ->
      reducible_values (push_one a theta' ++ theta) v T) ->
    (forall a, P a <-> reducible_values theta a A) ->
    reducible_values (push_all P theta' ++ theta) v T.
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
      t_rewrite_push_one ||
      ( progress unfold reduces_to in * ) ||
      find_smallstep_value ||
      apply strictly_positive_open ||
      apply left_lex ||
      find_exists ||
      find_exists2 ||
      ( progress autorewrite with bsize in * ) ||
      (rewrite reducible_unused_push_all in * by (steps; eauto using sat_p)) ||
      (rewrite reducible_unused_push_one in * by (eauto; steps)) ||
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
           pfv A type_var ::
           pfv T type_var ::
           support (push_all (fun a : tree => reducible_values theta a A) theta' ++ theta) ::
           support (push_all (fun a : tree => reducible_values theta a A) theta') ::
           support (push_all P theta' ++ theta) ::
           support (push_all P theta') ::
           support (push_one a theta') ::
           support theta' ::
           nil));
      repeat step || finisher || t_instantiate_rc || find_smallstep_value;
        try solve [ repeat unfold closed_term, closed_value in * || step ].

    lazymatch goal with
    | |- reducible_values ((?X,?RC) :: ?g1 ++ ?g2) _ (topen 0 ?T ?rep) =>
      apply reducible_rename with (topen 0 T rep) (g1 ++ (X,RC) :: g2)
                                  (idrel (X :: support g1 ++ support g2 ++ pfv T type_var))
    end;
      repeat step || apply valid_interpretation_append ||
             apply push_all_is_candidate || apply equivalent_with_relation_permute ||
             apply equal_with_relation_refl2 ||
             rewrite idrel_lookup || t_fv_open ||
             rewrite idrel_lookup_swap || t_fv_open ||
             t_listutils;
        eauto with b_valid_interp;
        eauto using reducibility_is_candidate;
        try solve [ unfold equivalent_rc; steps; eauto ];
        try solve [ apply valid_interpretation_all; eauto using sat_p ];
        try finisher.

    apply_induction HH;
      repeat
        step ||
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

    + apply reducible_unused3 in H14; repeat step || t_instantiate_reducible || simp_red || t_instantiate_rc ||
                                             t_deterministic_star ||
                                             unfold reduces_to in *; try finisher;
        eauto with b_red_is_val.
      apply reducible_rename_permute with X1;
        repeat step || eapply valid_interpretation_one || eauto || rewrite support_push_one in *; eauto with bapply_any;
          try finisher.

   + apply reducible_unused2; steps; try finisher; eauto with bapply_any.
   + apply reducible_unused3 in H14; repeat step; try finisher; eauto with bapply_any.

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
                       support theta' ::
                       pfv A type_var ::
                       pfv T2 type_var ::
                       pfv T3 type_var ::
                       pfv n'0 type_var ::
                       support (push_all P theta' ++ theta) ::
                       nil));
      repeat step || simp_red ||
             t_instantiate_reducible ||
             t_deterministic_star ||
             t_topen_none;
        eauto with omega;
        try finisher.

      repeat
        rewrite reducible_unused_middle in * by (
          repeat step || t_listutils ||
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

Hint Resolve valid_interpretation_append: b_valid_interp.
Hint Extern 1 => eapply valid_interpretation_one; eauto: b_valid_interp.

Ltac success t := (t; fail) || (t; []).

Ltac t_rewrite_unused_push_one :=
  rewrite reducible_unused_push_one in *; (
    repeat step || t_listutils || unfold no_type_fvar in * ||
           (rewrite is_erased_term_tfv in * by (steps; eauto with berased)) ||
           rewrite support_push_all in * || rewrite support_push_one in *;
    eauto using sat_p; eauto with bapply_any; try finisher
  ).

Ltac t_rewrite_unused_push_all :=
  rewrite reducible_unused_push_all in *; (
    repeat step || t_listutils || unfold no_type_fvar in * ||
           (rewrite is_erased_term_tfv in * by (steps; eauto with berased)) ||
           rewrite support_push_all in * || rewrite support_push_one in *;
    eauto using sat_p; eauto with bapply_any; try finisher
  ).

      eapply reducible_rename_one_rc; eauto;
        repeat step ||
               (success t_rewrite_unused_push_all) ||
               (success t_rewrite_unused_push_one) ||
               apply reducibility_is_candidate ||
               unfold equivalent_rc;
        eauto using sat_p with b_valid_interp bapply_any;
        try finisher.

  (** Recursive type at n+1: case where the recursive type is itself strictly positive **)
  - right.
      exists n'0, v'0, (makeFresh (
                       support theta ::
                       support theta' ::
                       pfv A type_var ::
                       pfv T2 type_var ::
                       pfv T3 type_var ::
                       pfv n'0 type_var ::
                       support (push_all P theta' ++ theta) ::
                       nil));
      repeat step || simp_red ||
             t_instantiate_reducible ||
             t_deterministic_star ||
             t_topen_none;
        eauto with omega;
        try finisher.

      remember  (makeFresh (
                       support theta ::
                       support theta' ::
                       pfv A type_var ::
                       pfv T2 type_var ::
                       pfv T3 type_var ::
                       pfv n'0 type_var ::
                       support (push_all P theta' ++ theta) ::
                       nil)) as M.


      erewrite push_all_cons.
      apply HH.
