Require Import Equations.Equations.
Require Import Equations.Prop.Subterm.

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Export SystemFR.ReducibilityUnused.

Require Import PeanoNat.

Open Scope list_scope.

Opaque makeFresh.
Opaque reducible_values.
Opaque lt.

Require Import Omega.

(* TODO: rewrite proof following ReducibilityRenaming's model *)

Lemma fv_red:
  forall t x tag theta T,
    valid_interpretation theta ->
    reducible_values theta t T ->
    x ∈ pfv t tag ->
    False.
Proof.
  intros; erewrite reducible_val_fv in *; eauto; steps.
Qed.

Ltac t_fv_red :=
  match goal with
  | H1: valid_interpretation ?theta, H2: reducible_values ?theta ?t _, H3: _ ∈ pfv ?t _ |- _ =>
    apply False_ind; apply (fv_red _ _ _ _ _ H1 H2 H3)
  end.

Set Program Mode.

Ltac t_apply_ih_sub :=
  lazymatch goal with
  | IHn: forall m, _ -> forall theta U V X v P, _,
     H1: reducible_values ?theta ?t (T_rec ?n (psubstitute ?T0 _ type_var) (psubstitute ?Ts _ type_var)) |-
     reducible_values ?theta ?t (T_rec ?n ?T0 ?Ts)  =>
       poseNew (Mark 0 "IHOncee");
       unshelve eapply (IHn (get_measure (T_rec n T0 Ts)) _ theta (T_rec n T0 Ts) V X t P); eauto
  | IHn: forall m, _ -> forall theta U V X v P, _,
     H1: reducible_values ?theta ?t (T_rec ?n ?T0 ?Ts) |-
     reducible_values ?theta ?t (T_rec ?n (psubstitute ?T0 _ type_var) (psubstitute ?Ts _ type_var))  =>
       poseNew (Mark 0 "IHOnce");
       unshelve eapply (IHn (get_measure (T_rec n T0 Ts)) _ theta (T_rec n T0 Ts) V X t P) in H1; eauto
  end.

Lemma reducibility_subst_aux:
  forall (measure: measure_domain) (theta: interpretation) U V X v P,
    get_measure U = measure ->
    twf V 0 ->
    wf V 0 ->
    is_erased_type U ->
    valid_interpretation theta ->
    lookup Nat.eq_dec theta X = Some P ->
    is_erased_type V ->
    (forall (t: tree), P t <-> reducible_values theta t V) ->
    reducible_values theta v U <-> reducible_values theta v (psubstitute U ((X,V) :: nil) type_var).
Proof.
  induction measure using measure_induction; destruct U;
    repeat match goal with
           | _ => progress (step || simp_red)
           | _ => find_smallstep_value || find_exists
           | _ => apply left_lex
           | _ => rewrite substitute_nothing5 in * by (steps; eauto with fv)
           | _ => rewrite substitute_open2 in *  by repeat step || t_fv_red || rewrite is_erased_term_tfv in * by (steps; eauto with erased)
           | _ => progress ( autorewrite with bsize in * )
           | H: is_erased_term ?t |- _ => rewrite (is_erased_subst t) in *
           | _ => apply erased_is_erased
           | _ => rewrite erased_term_tfv in *
           | _: is_erased_term ?b, H: forall a, _ -> _ -> reduces_to (fun t => reducible_values ?theta t (open 0 ?T _)) _ |-
                 reduces_to _ _ =>
                   poseNew (Mark 0 "reduces_to_equiv");
                   apply reduces_to_equiv with (fun t => reducible_values theta t (open 0 T b))
           | H: forall a, _ -> reduces_to _ _ |- _ => apply H
           | H: forall a, _ -> reducible_values _ _ _ |- _ => apply H
(*           | H: star scbv_step _ ?a |- _ => unshelve exists a *)
           | H: reducible_values _ ?t ?T |- reducible_values _ ?t (psubstitute ?T _ _) \/ _ => left
           | H: reducible_values _ ?t (psubstitute ?T _ _) |- reducible_values _ ?t ?T \/ _ => left
           | H: reducible_values _ ?t ?T |- _ \/ reducible_values _ ?t (psubstitute ?T _ _) => right
           | H: reducible_values _ ?t (psubstitute ?T _ _) |- _ \/ reducible_values _ ?t ?T => right
           | H: star scbv_step _ zero |- _ \/ _ => left
           | |- (exists v, tleft ?v' = tleft v /\ _) \/ _ => left; exists v'
           | |- _ \/ (exists v, tright ?v' = tright v /\ _) => right; exists v'
           | H: reducible_values ?theta ?a ?U |- exists x _, reducible_values ?theta x (psubstitute ?U _ _) /\ _ => exists a
           | H: reducible_values ?theta ?a (psubstitute ?U _ _) |- exists x _, reducible_values ?theta x ?U /\ _ => exists a
           | H: reducible_values ?theta ?a ?U |- exists x, reducible_values ?theta x (psubstitute ?U _ _) => exists a
           | H: reducible_values ?theta ?a (psubstitute ?U _ _) |- exists x, reducible_values ?theta x ?U => exists a
           | H1: forall a, _ -> reducible_values _ _ _ -> _,
             H2: is_erased_term ?a  |- _ =>
               poseNew (Mark H1 "instantiate");
               unshelve epose proof (H1 a _ _)
           | IHn: forall m, _ -> forall theta U V X v P, _,
             H1: reducible_values ?theta ?t (psubstitute ?T ((?X,?V) :: nil) type_var) |-
               reducible_values ?theta ?t ?T =>
                 unshelve eapply (IHn (get_measure T) _ theta T V X t P); eauto
           | IHn: forall m, _ -> forall theta U V X v P, _,
             H1: reducible_values ?theta ?t ?T |-
               reducible_values ?theta ?t (psubstitute ?T ((?X,?V) :: nil) type_var) =>
                 unshelve eapply (IHn (get_measure T) _ theta T V X t P); eauto
           | |- exists c d _, pp ?a ?b = pp _ _ /\ _ => unshelve exists a, b
           | |- exists x, tfold ?v = tfold x /\ _ => unshelve exists v
(*           | H: is_erased_term ?a |- _ => unshelve exists a (* !!! *) *)
           end;
      eauto with wf;
      eauto with erased;
      try omega;
      try solve [ apply_any; auto ].

    - (* polymorphic type *)
      exists (makeFresh ((X :: nil) :: support theta :: pfv V type_var :: pfv U type_var :: pfv (psubstitute U ((X, V) :: nil) type_var) type_var :: nil)); repeat step || finisher.
      instantiate_any.
      lazymatch goal with
      | H: reducible_values _ _ _ |- reducible_values ((?M,?RC) :: _) _ _ =>
        apply (reducible_rename_one _ _ _ _ _ M) in H
      end;
        repeat step || finisher || rewrite substitute_topen2.

      lazymatch goal with
      | IHn: forall m, _ -> forall theta U V X v P, _,
        H1: reducible_values ?theta ?t ?T |-
          reducible_values ?theta ?t (psubstitute ?T ((?X,?V) :: nil) type_var) =>
            unshelve eapply (IHn (get_measure T) _ theta T V X t P)
      end;
        repeat step || autorewrite with bsize in * ||
               apply reducible_unused2 || t_fv_open || t_listutils ||
               apply left_lex ||
               finisher || apply is_erased_type_topen;
          try omega;
          eauto with apply_any.

       match goal with
       | H: _ |- _ => apply reducible_unused3 in H
       end; repeat step || finisher || apply_any.

    - (* polymorphic type (2) *)
      exists (makeFresh ((X0 :: nil) :: (X :: nil) :: support theta :: pfv V type_var :: pfv U type_var :: pfv (psubstitute U ((X, V) :: nil) type_var) type_var :: nil)); repeat step || finisher.
      instantiate_any.

      lazymatch goal with
      | H: reducible_values _ _ _ |- reducible_values ((?M,?RC) :: _) _ _ =>
        apply (reducible_rename_one _ _ _ _ _ M) in H
      end; repeat step || finisher.

      lazymatch goal with
      | H: reducible_values _ _ _ |- _ =>
        rewrite substitute_topen2 in H by repeat step || finisher
      end.
      lazymatch goal with
      | IHn: forall m, _ -> forall theta U V X v P, _,
        H1: reducible_values ?theta ?t (psubstitute ?T ((?X,?V) :: nil) type_var) |-
          reducible_values ?theta ?t ?T =>
            unshelve eapply (IHn (get_measure T) _ theta T V X t P)
      end;
        repeat step || autorewrite with bsize in * ||
               apply reducible_unused2 || t_fv_open || t_listutils ||
               finisher || apply is_erased_type_topen || apply left_lex;
          try omega;
          eauto with apply_any.

       match goal with
       | H: _ |- _ => apply reducible_unused3 in H
       end; repeat step || finisher || apply_any.

    - (* recursive type n+1 *)
      right.
      unshelve eexists n', (makeFresh ((X :: nil) :: pfv V type_var :: pfv U2 type_var :: pfv U3 type_var
                                                     :: pfv (psubstitute U2 ((X, V) :: nil) type_var) type_var
                                                     :: pfv (psubstitute U3 ((X, V) :: nil) type_var) type_var
                                                     :: support theta :: nil)), _, _; eauto;
        repeat step || finisher.

      lazymatch goal with
      | H: reducible_values _ _ _ |- reducible_values ((?M,?RC) :: _) _ _ =>
        apply (reducible_rename_one_rc _ RC _ _ _ _ M) in H
      end;
        repeat step || finisher || apply is_erased_type_topen ||
                  rewrite substitute_topen2 || t_apply_ih_sub ||
                  match goal with
                  | H: is_nat_value ?v, H2: context[psubstitute ?v _ _] |- _ =>
                    rewrite (substitute_nothing5 v) in H2 by eauto with fv
                  | H: is_nat_value ?v |- context[psubstitute ?v _ _] =>
                    rewrite (substitute_nothing5 v) by eauto with fv
                  end ||
                  unfold EquivalentWithRelation.equivalent_rc;
        eauto using reducibility_is_candidate;
        try solve [ apply leq_lt_measure; autorewrite with bsize in *; omega ];
        try solve [ apply right_lex, right_lex, lt_index_step; auto ];
        try solve [ apply left_lex; autorewrite with bsize in *; omega ];
        try solve [ apply right_lex, lt_index_step; auto ];
        eauto with erased.

      lazymatch goal with
      | IHn: forall m, _ -> forall theta U V X v P, _,
        H1: reducible_values ?theta ?t ?T |-
          reducible_values ?theta ?t (psubstitute ?T ((?X,?V) :: nil) type_var) =>
            unshelve eapply (IHn (get_measure T) _ theta T V X t P)
      end;
        repeat step || autorewrite with bsize in * ||
               apply reducible_unused2 || t_fv_open || t_listutils ||
               apply left_lex ||
               finisher || apply is_erased_type_topen;
          try omega;
          eauto with apply_any;
          eauto using reducibility_is_candidate.

       match goal with
       | H: _ |- _ => apply reducible_unused3 in H
       end; repeat step || finisher || apply_any;
         eauto using reducibility_is_candidate.

    - (* recursive type n+1 bis *)
      right.
      unshelve eexists n', (makeFresh ((X :: nil) :: pfv V type_var :: pfv U3 type_var :: pfv U2 type_var
                                                     :: pfv (psubstitute U3 ((X, V) :: nil) type_var) type_var
                                                     :: pfv (psubstitute U2 ((X, V) :: nil) type_var) type_var
                                                     :: support theta :: nil)), _, _; eauto;
        repeat step || finisher.

      lazymatch goal with
      | H: reducible_values _ _ _ |- reducible_values ((?M,?RC) :: _) _ _ =>
        apply (reducible_rename_one_rc _ RC _ _ _ _ M) in H
      end;
        repeat step || finisher || apply is_erased_type_topen ||
                  t_apply_ih_sub ||
                  match goal with
                  | H: is_nat_value ?v, H2: context[psubstitute ?v _ _] |- _ =>
                    rewrite (substitute_nothing5 v) in H2 by eauto with fv
                  | H: is_nat_value ?v |- context[psubstitute ?v _ _] =>
                    rewrite (substitute_nothing5 v) by eauto with fv
                  end ||
                  unfold EquivalentWithRelation.equivalent_rc;
        eauto using reducibility_is_candidate;
        try solve [ apply leq_lt_measure; autorewrite with bsize in *; omega ];
        try solve [ apply right_lex, right_lex, lt_index_step; auto ];
        try solve [ apply left_lex; autorewrite with bsize in *; omega ];
        try solve [ apply right_lex, lt_index_step; auto ];
        eauto with erased.

      lazymatch goal with
      | H: reducible_values _ _ _ |- _ =>
        rewrite substitute_topen2 in H by repeat step || finisher
      end.

      lazymatch goal with
      | IHn: forall m, _ -> forall theta U V X v P, _,
        H1: reducible_values ?theta ?t (psubstitute ?T ((?X,?V) :: nil) type_var) |-
          reducible_values ?theta ?t ?T =>
            unshelve eapply (IHn (get_measure T) _ theta T V X t P)
      end;
        repeat step || autorewrite with bsize in * ||
               apply reducible_unused2 || t_fv_open || t_listutils ||
               apply left_lex ||
               finisher || apply is_erased_type_topen;
          try omega;
          eauto with apply_any;
          eauto using reducibility_is_candidate.

       match goal with
       | H: _ |- _ => apply reducible_unused3 in H
       end; repeat step || finisher || apply_any;
         eauto using reducibility_is_candidate.
Qed.

Lemma reducibility_subst:
  forall (theta: interpretation) U V X v P,
    valid_interpretation theta ->
    twf V 0 ->
    wf V 0 ->
    is_erased_type U ->
    is_erased_type V ->
    lookup Nat.eq_dec theta X = Some P ->
    (forall (t: tree), P t <-> reducible_values theta t V) ->
    reducible_values theta v U <-> reducible_values theta v (psubstitute U ((X,V) :: nil) type_var).
Proof.
  eauto using reducibility_subst_aux.
Qed.

Lemma reducibility_subst_head:
  forall (theta : interpretation) U V X v,
    reducible_values ((X, fun v => reducible_values theta v V) :: theta) v
                     (topen 0 U (fvar X type_var)) ->
    valid_interpretation theta ->
    (X ∈ pfv U type_var -> False) ->
    (X ∈ pfv V type_var -> False) ->
    twf V 0 ->
    wf V 0 ->
    is_erased_type U ->
    is_erased_type V ->
    reducible_values theta v (topen 0 U V).
Proof.
  intros.
  apply reducible_unused3 with X (fun v => reducible_values theta v V);
    repeat step || t_fv_open  || t_listutils;
    eauto using reducibility_is_candidate.

  lazymatch goal with
  | H: reducible_values ((?X,?RC) :: ?theta) ?v ?U |- _ =>
    unshelve epose proof (proj1 (
      reducibility_subst ((X,RC) :: theta) U V X v
                         (fun v => reducible_values theta v V)
                         _ _ _ _ _ _ _) H)
  end;
    repeat tac1 || rewrite substitute_nothing3 in *;
      eauto using reducibility_is_candidate;
      try solve [ eapply reducible_unused2; steps; eauto using reducibility_is_candidate ];
      try solve [ eapply reducible_unused3 with X _; steps; eauto using reducibility_is_candidate ];
      eauto 2 with erased step_tactic.
Qed.

Lemma reducibility_subst_head2:
  forall (theta : interpretation) U V X v,
    valid_interpretation theta ->
    (X ∈ pfv U type_var -> False) ->
    (X ∈ pfv V type_var -> False) ->
    twf V 0 ->
    wf V 0 ->
    is_erased_type U ->
    is_erased_type V ->
    reducible_values theta v (topen 0 U V) ->
    reducible_values ((X, fun v => reducible_values theta v V) :: theta) v
                     (topen 0 U (fvar X type_var)).
Proof.
  intros.
  apply (reducible_unused2 _ _ X _ (fun v => reducible_values theta v V)) in H6;
    repeat step || t_fv_open  || t_listutils;
    eauto using reducibility_is_candidate.

  lazymatch goal with
  | H: reducible_values _ _ _ |- reducible_values ((?X,?RC) :: ?theta) ?v ?U =>
    unshelve epose proof (
      reducibility_subst ((X,RC) :: theta) U V X v
                         (fun v => reducible_values theta v V)
                         _ _ _ _ _ _ _)
  end;
    repeat tac1 || rewrite substitute_nothing3 in *;
      eauto using reducibility_is_candidate;
      try solve [ eapply reducible_unused2; steps; eauto using reducibility_is_candidate ];
      try solve [ eapply reducible_unused3 with X _; steps; eauto using reducibility_is_candidate ];
      eauto 2 with erased step_tactic.
Qed.
