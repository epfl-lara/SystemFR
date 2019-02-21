Require Import Equations.Equations.
Require Import Equations.Subterm.

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import Termination.Syntax.
Require Import Termination.Tactics.
Require Import Termination.Sets.
Require Import Termination.TermList.
Require Import Termination.AssocList.
Require Import Termination.SizeLemmas.
Require Import Termination.ListUtils.
Require Import Termination.SmallStep.
Require Import Termination.StarRelation.
Require Import Termination.SubstitutionLemmas.
Require Import Termination.Freshness.
Require Import Termination.Equivalence.
Require Import Termination.IdRelation.
Require Import Termination.SetLemmas.
Require Import Termination.EqualWithRelation.
Require Import Termination.EquivalentWithRelation.
Require Import Termination.ErasedTermLemmas.

Require Import Termination.FVLemmas.
Require Import Termination.FVLemmasLists.

Require Import Termination.ReducibilityCandidate.
Require Import Termination.ReducibilityDefinition.
Require Import Termination.ReducibilityLemmas.
Require Import Termination.ReducibilityMeasure.

Require Import Termination.RedTactics.

Require Import PeanoNat.

Require Import Omega.

Open Scope list_scope.

Opaque reducible_values.
Opaque makeFresh.
Opaque lt.

Ltac t_apply_ih :=
  lazymatch goal with
  | IH: forall m, _ -> forall T T' t theta theta' l, _ ,
    H1: reducible_values ?theta' ?t ?T',
    H2: equal_with_relation ?rel ?T ?T' |-
      reducible_values ?theta ?t ?T =>
        unshelve eapply (IH (size T, index T) _ T T' t theta theta' rel); eauto
  | IH: forall m, _ -> forall T T' t theta theta' l, _ ,
    H1: reducible_values ?theta ?t ?T,
    H2: equal_with_relation ?rel ?T ?T' |-
      reducible_values ?theta' ?t ?T' =>
        unshelve eapply (IH (size T, index T) _ T T' t theta theta' rel); eauto
  end.

Ltac t_apply_ih2 :=
  lazymatch goal with
  | IH: forall m, _ -> forall T T' t theta theta' l, _ ,
    H1: reducible_values ?theta' ?t ?T',
    H2: equivalent_with_relation ?rel ?theta ?theta' |-
      reducible_values ?theta ?t ?T =>
        unshelve eapply (IH (size T, index T) _ T T' t theta theta' rel); eauto
  | IH: forall m, _ -> forall T T' t theta theta' l, _ ,
    H1: reducible_values ?theta ?t ?T,
    H2: equivalent_with_relation ?rel ?theta ?theta' |-
      reducible_values ?theta' ?t ?T' =>
        unshelve eapply (IH (size T, index T) _ T T' t theta theta' rel); eauto
  end.

Set Program Mode.

Ltac t_bewr_constructor :=
  match goal with
  | |- equal_with_relation _ _ _ => constructor
  end.

Lemma reducible_rename_aux:
  forall measure T T' t (theta theta' : interpretation) rel,
    (size T, index T) = measure ->
    valid_interpretation theta ->
    valid_interpretation theta' ->
    equivalent_with_relation rel theta theta' ->
    equal_with_relation rel T T' ->
    (
      reducible_values theta t T <->
      reducible_values theta' t T'
    ).
Proof.
  induction measure using measure_induction; intros; destruct T;
      repeat match goal with
      | _ => step || t_fv_open ||  simp_red || t_listutils || t_lookup || destruct_tag
      | _ => apply equal_with_relation_open
      | _ => apply left_lex
      | _ => t_instantiate_rel
      | _ => t_lookup_same
      | _ => t_equal_with_erased
      | _ => step_inversion equal_with_relation
      | _ => t_apply_ih
      | _ => find_exists || find_smallstep_value
      | H: is_erased_term ?t |- _ => rewrite (is_erased_subst t) in *
      | _ => apply erased_is_erased
      | _ => rewrite erased_term_tfv in *
      | _ => progress ( autorewrite with bsize in * )
      | _ => rewrite substitute_open2 in * by
            (repeat step || ( rewrite erased_term_tfv in * ) ||
                    eauto using is_renaming_twfs, is_renaming_wfs)
      | IH: forall m, _ -> forall T T' t theta theta' l, _ ,
        H1: reducible_values ?theta' ?t (open 0 ?T' ?a) ,
        H2: equal_with_relation ?rel ?T ?T' |-
          reducible_values ?theta ?t (open 0 ?T ?a) =>
            unshelve eapply (IH _ _ (open 0 T a) (open 0 T' a) t theta theta' rel); eauto
      | IH: forall m, _ -> forall T T' t theta theta' l, _ ,
        H1: reducible_values ?theta ?t (open 0 ?T ?a),
        H2: equal_with_relation ?rel ?T ?T' |-
          reducible_values ?theta' ?t (open 0 ?T' ?a) =>
            unshelve eapply (IH _ _ (open 0 T a) (open 0 T' a) t theta theta' rel); eauto
      | _: is_erased_term ?b, H: forall a, _ -> _ -> reduces_to (fun t => reducible_values ?theta t (open 0 ?T _)) _ |-
          reduces_to _ _ =>
        poseNew (Mark 0 "reduces_to_equiv");
        apply reduces_to_equiv with (fun t => reducible_values theta t (open 0 T b))
      | |- _ ∈ support _ => apply_any
      | H: forall a, _ -> reduces_to _ _ |- _ => apply H
      | H: forall a, _ -> reducible_values _ _ _ |- _ => apply H
      | H1: forall a, is_erased_term a -> reducible_values _ _ _ -> _,
        H2: is_erased_term ?a  |- _ =>
          poseNew (Mark H1 "instantiate");
          unshelve epose proof (H1 a _ _)
      | |- exists c d _, pp ?a ?b = pp _ _ /\ _ => unshelve exists a, b
      | H: star small_step _ ?a |- _ => is_var a; unshelve exists a (* !! *)
(*      | H: is_erased_term ?a |- _ => unshelve exists a (* !! *) *)
      | H1: equal_with_relation _ ?T ?T',
        H: reducible_values _ ?t ?T |- exists _ _, reducible_values _ _ ?T' /\ _ => exists t
      | H1: equal_with_relation _ ?T' ?T,
        H: reducible_values _ ?t ?T |- exists _ _, reducible_values _ _ ?T' /\ _ => exists t
      | H1: equal_with_relation _ ?T ?T',
        H: reducible_values _ ?t ?T |- reducible_values _ ?t ?T' \/ _ => left
      | H1: equal_with_relation _ ?T' ?T,
        H: reducible_values _ ?t ?T |- reducible_values _ ?t ?T' \/ _ => left
      | H1: equal_with_relation _ ?T ?T',
        H: reducible_values _ ?t ?T |- _ \/ reducible_values _ ?t ?T' => right
      | H1: equal_with_relation _ ?T' ?T,
        H: reducible_values _ ?t ?T |- _ \/ reducible_values _ ?t ?T' => right
      | H: star small_step _ zero |- _ \/ _ => left
      | H: star small_step _ (succ _) |- _ => right
      | H1: equal_with_relation ?rel ?T ?T' |- exists X, (X ∈ ?L -> False) /\ _ =>
          exists (makeFresh (L :: (range rel) :: (range (swap rel)) :: (pfv T type_var) :: (pfv T' type_var) :: nil))
      | |- (exists v, tleft ?v' = tleft v /\ _) \/ _ => left; exists v'
      | |- _ \/ (exists v, tright ?v' = tright v /\ _) => right; exists v'
      end;
      try omega;
      try finisher;
      eauto with falsity;
      eauto with bwf;
      eauto with bfv;
      try solve [ eapply equivalent_rc_left; eauto 1 ];
      try solve [ eapply equivalent_rc_right; eauto 1 ].

    - instantiate_any. eapply reduces_to_equiv; eauto 1; steps.
      lazymatch goal with
      | IH: forall m, _ -> forall T T' t theta theta' rel, _ ,
        H1: reducible_values ((?X,?RC) :: ?theta) ?t ?T,
        H2: equal_with_relation ?rel _ _ |-
          reducible_values ((?M,?RC) :: ?theta') ?t ?T' =>
            unshelve epose proof
              (IH (size T, index T) _ T T' t
                   ((X,RC) :: theta)
                   ((M,RC) :: theta')
                   ((X,M) :: rel)
                   _ _ _ _ _
              )
      end;
        repeat
          steps || (progress autorewrite with bsize in * ) || t_fv_open || t_listutils ||
          apply equivalent_with_relation_add || finisher ||
          apply equal_with_relation_topen ||
          apply left_lex ||
          (rewrite substitute_topen3 in * by steps);
        try omega;
        eauto using in_remove_support;
        eauto using equivalent_rc_refl.

    - instantiate_any. eapply reduces_to_equiv; eauto 1; steps.
      lazymatch goal with
      | IH: forall m, _ -> forall T T' t theta theta' rel, _ ,
        H1: reducible_values ((?X,?RC) :: ?theta) ?t ?T,
        H2: equal_with_relation ?rel _ _ |-
          reducible_values ((?M,?RC) :: ?theta') ?t ?T' =>
            unshelve epose proof
              (IH (size T, index T) _ T T' t
                   ((X,RC) :: theta)
                   ((M,RC) :: theta')
                   ((X,M) :: (swap rel))
                   _ _ _ _ _
              )
      end;
        repeat
          steps || (progress autorewrite with bsize in * ) || t_fv_open || t_listutils ||
          apply equivalent_with_relation_add || finisher ||
          apply equal_with_relation_topen ||
          apply equivalent_with_relation_swap ||
          apply equal_with_relation_swap ||
          apply left_lex ||
          match goal with
          | H: equal_with_relation _ _ _ |- _ =>
            rewrite (equal_with_relation_size _ _ _ H) in * by steps
          end ||
          (rewrite substitute_topen3 in * by steps);
        try omega;
        eauto using in_remove_support;
        eauto using equivalent_rc_refl.

  - (* case recursive type at n + 1 *)
    unshelve eexists n', v', (makeFresh (pfv T0' type_var :: pfv Ts' type_var ::  support theta' :: nil)), _, _; eauto;
      repeat step || finisher.
    lazymatch goal with
    | IH: forall m, _ -> forall T T' t theta theta' rel, _ ,
      H1: reducible_values ((?X,?RC1) :: ?theta) ?t ?T,
      H2: equal_with_relation ?rel _ _ |-
        reducible_values ((?M,?RC2) :: ?theta') ?t ?T' =>
          unshelve epose proof
            (IH (size T, index T) _ T T' t
                 ((X,RC1) :: theta)
                 ((M,RC2) :: theta')
                 ((X,M) :: rel)
                 _ _ _ _ _
            )
    end;
      repeat
        steps || (progress autorewrite with bsize in * ) || t_fv_open || t_listutils ||
        apply equivalent_with_relation_add || finisher ||
        apply equal_with_relation_topen ||
        unfold equivalent_rc ||
        apply equal_with_relation_refl ||
        (rewrite substitute_topen3 in * by steps) ||
        t_apply_ih2 || t_bewr_constructor;
      try solve [ apply left_lex; omega ];
      try solve [ apply right_lex; apply lt_index_step; auto ];
      eauto using in_remove_support;
      eauto using reducibility_is_candidate;
      eauto with bfv.

  - (* case recursive type at n + 1 *)
   unshelve eexists n'0, v', (makeFresh (pfv T2 type_var :: pfv T3 type_var :: support theta :: nil)), _, _; eauto;
      repeat step || finisher.
    lazymatch goal with
    | IH: forall m, _ -> forall T T' t theta theta' rel, _ ,
      H1: reducible_values ((?X,?RC1) :: ?theta) ?t ?T,
      H2: equal_with_relation ?rel _ _ |-
        reducible_values ((?M,?RC2) :: ?theta') ?t ?T' =>
          unshelve epose proof
            (IH (size T, index T) _ T T' t
                 ((X,RC1) :: theta)
                 ((M,RC2) :: theta')
                 ((X,M) :: (swap rel))
                 _ _ _ _ _
            )
    end;
      repeat
        steps || (progress autorewrite with bsize in * ) || t_fv_open || t_listutils ||
        apply equivalent_with_relation_add || finisher ||
        apply equal_with_relation_topen ||
        unfold equivalent_rc ||
        apply equivalent_with_relation_swap ||
        apply equal_with_relation_swap ||
        apply equal_with_relation_refl ||
        match goal with
        | H: equal_with_relation _ _ _ |- _ =>
          rewrite (equal_with_relation_size _ _ _ H) in * by steps
        end ||
        (rewrite substitute_topen3 in * by steps) ||
        t_apply_ih2 || t_bewr_constructor;
      try solve [ apply left_lex; omega ];
      try solve [ apply right_lex; apply lt_index_step; auto ];
      eauto using in_remove_support;
      eauto using reducibility_is_candidate;
      eauto with bfv.
Qed.

Lemma reducible_rename :
  forall T T' t (theta theta' : interpretation) rel,
    reducible_values theta t T ->
    valid_interpretation theta ->
    valid_interpretation theta' ->
    equivalent_with_relation rel theta theta' ->
    equal_with_relation rel T T' ->
    reducible_values theta' t T'     .
Proof.
  intros; eapply (reducible_rename_aux _ T T' t theta theta' rel); eauto.
Qed.

Lemma reducible_rename_one:
  forall RC theta v T X Y,
    reducible_values ((X,RC) :: theta) v (topen 0 T (fvar X type_var)) ->
    valid_interpretation theta ->
    reducibility_candidate RC ->
    (X ∈ pfv T type_var -> False) ->
    (Y ∈ pfv T type_var -> False) ->
    reducible_values ((Y,RC) :: theta) v (topen 0 T (fvar Y type_var)).
Proof.
  intros.
  eapply (reducible_rename _ _ _ _ _ ((X,Y) :: idrel (pfv T type_var))); eauto;
    repeat step || t_idrel || t_lookup ||
           apply equivalent_with_relation_add ||
           apply equal_with_relation_topen ||
           apply equal_with_idrel ||
           unfold equivalent_with_relation;
           eauto using equivalent_rc_refl;
           eauto using equivalent_rc_at_refl.
Qed.

Lemma reducible_rename_one_rc:
  forall RC RC' theta v T X Y,
    reducible_values ((X,RC) :: theta) v (topen 0 T (fvar X type_var)) ->
    valid_interpretation theta ->
    reducibility_candidate RC ->
    reducibility_candidate RC' ->
    equivalent_rc RC RC' ->
    (X ∈ pfv T type_var -> False) ->
    (Y ∈ pfv T type_var -> False) ->
    reducible_values ((Y,RC') :: theta) v (topen 0 T (fvar Y type_var)).
Proof.
  intros.
  eapply (reducible_rename _ _ _ _ _ ((X,Y) :: idrel (pfv T type_var))); eauto;
    repeat step || t_idrel || t_lookup ||
           apply equivalent_with_relation_add ||
           apply equal_with_relation_topen ||
           apply equal_with_idrel ||
           unfold equivalent_with_relation;
           eauto using equivalent_rc_refl;
           eauto using equivalent_rc_at_refl.
Qed.

Lemma reducible_rename_permute:
  forall T theta1 theta2 X Y (RC : tree -> Prop) v,
    valid_interpretation theta1 ->
    valid_interpretation theta2 ->
    reducibility_candidate RC ->
    ~(Y ∈ support theta1) ->
    ~(X ∈ pfv T type_var) ->
    ~(Y ∈ pfv T type_var) ->
    reducible_values ((X, RC) :: theta1 ++ theta2) v (topen 0 T (fvar X type_var)) ->
    reducible_values (theta1 ++ (Y, RC) :: theta2) v (topen 0 T (fvar Y type_var)).
Proof.
  intros.
  eapply (reducible_rename _ _ _ _ _ ((X,Y) :: idrel (pfv T type_var))); eauto;
    repeat step || apply valid_interpretation_append || apply equal_with_relation_topen;
    eauto using equal_with_idrel.

  +
  apply equivalent_with_relation_permute2; steps.
Qed.
