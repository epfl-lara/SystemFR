Require Import Equations.Equations.

Require Import Coq.Strings.String.

Require Import Termination.Syntax.
Require Import Termination.Tactics.
Require Import Termination.Sets.
Require Import Termination.TermList.
Require Import Termination.AssocList.
Require Import Termination.TermForm.
Require Import Termination.SizeLemmas.
Require Import Termination.ListUtils.
Require Import Termination.SmallStep.
Require Import Termination.StarRelation.
Require Import Termination.SubstitutionLemmas.
Require Import Termination.TypeErasure.
Require Import Termination.TypeErasureLemmas.

Require Import Termination.FVLemmas.
Require Import Termination.FVLemmasLists.

Require Import Termination.WFLemmas.

Require Import Termination.ReducibilityCandidate.
Require Import Termination.ReducibilityDefinition.
Require Import Termination.ReducibilityLemmas.
Require Import Termination.ReducibilityUnused.
Require Import Termination.ReducibilityRenaming.
Require Import Termination.RedTactics.

Require Import Termination.IdRelation.
Require Import Termination.Freshness.

Require Import PeanoNat.

Open Scope list_scope.

Opaque makeFresh.
Opaque reducible_values.

Require Import Omega.

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

Lemma reducibility_subst_aux:
  forall n (theta: interpretation) U V X v P,
    size U < n ->
    twf V 0 ->
    wf V 0 ->
    is_erased_type U ->
    valid_interpretation theta ->
    lookup Nat.eq_dec theta X = Some P ->
    (forall (t: tree), P t <-> reducible_values theta t V) ->
    reducible_values theta v U <-> reducible_values theta v (psubstitute U ((X,V) :: nil) type_var).
Proof.
  induction n; eauto with omega;
    destruct U;
    repeat match goal with
           | _ => progress (step || simp_red)
           | _ => rewrite substitute_open2 in * by (repeat step || t_fv_red)
           | _ => rewrite substitute_nothing5 in * by (steps; eauto with bfv)
           | _ => rewrite substitute_open2 in *  by repeat step || t_fv_red || rewrite is_erased_term_tfv in * by (steps; eauto with berased)
           | _ => progress ( autorewrite with bsize in * )
           | H: is_erased_term ?t |- _ => rewrite (is_erased_subst t) in *
           | _ => apply erased_is_erased
           | _ => rewrite erased_term_tfv in *
           | b: erased_term, H: forall a, _ -> reduces_to (fun t => reducible_values ?theta t (open 0 ?T _)) _ |-
                 reduces_to _ _ =>
                   poseNew (Mark 0 "reduces_to_equiv");
                   apply reduces_to_equiv with (fun t => reducible_values theta t (open 0 T b))
           | H: forall a, _ -> reduces_to _ _ |- _ => apply H
           | H: forall a, _ -> reducible_values _ _ _ |- _ => apply H
           | H: star small_step _ ?a |- _ => unshelve exists a
           | H: reducible_values _ ?t ?T |- reducible_values _ ?t (psubstitute ?T _ _) \/ _ => left
           | H: reducible_values _ ?t (psubstitute ?T _ _) |- reducible_values _ ?t ?T \/ _ => left
           | H: reducible_values _ ?t ?T |- _ \/ reducible_values _ ?t (psubstitute ?T _ _) => right
           | H: reducible_values _ ?t (psubstitute ?T _ _) |- _ \/ reducible_values _ ?t ?T => right
           | H1: forall a, reducible_values _ _ _ -> _,
             a: erased_term  |- _ =>
               poseNew (Mark H1 "instantiate");
               unshelve epose proof (H1 a _)
           | IHn: forall theta U V X v P, _,
             H1: reducible_values ?theta ?t (psubstitute ?T ((?X,?V) :: nil) type_var) |-
               reducible_values ?theta ?t ?T =>
                 apply (IHn theta T V X t P)
           | IHn: forall theta U V X v P, _,
             H1: reducible_values ?theta ?t ?T |-
               reducible_values ?theta ?t (psubstitute ?T ((?X,?V) :: nil) type_var) =>
                 apply (IHn theta T V X t P)
           | |- exists c d, pp ?a ?b = pp _ _ /\ _ => unshelve exists a, b
           | a: erased_term |- _ => unshelve exists a (* !!! *)
           end;
      eauto with bwf;
      eauto with berased;
      try omega;
      try solve [ apply_any; auto ].

    - exists (makeFresh ((X :: nil) :: support theta :: pfv V type_var :: pfv U type_var :: pfv (psubstitute U [(X, V)] type_var) type_var :: nil)); repeat step || finisher.
      instantiate_any; eapply reduces_to_equiv; eauto 1; steps.
      lazymatch goal with
      | H: reducible_values _ _ _ |- reducible_values ((?M,?RC) :: _) _ _ =>
        apply (reducible_rename_one _ _ _ _ _ M) in H
      end;
        repeat step || finisher || rewrite substitute_topen2.

      lazymatch goal with
      | IHn: forall theta U V X v P, _,
        H1: reducible_values ?theta ?t ?T |-
          reducible_values ?theta ?t (psubstitute ?T ((?X,?V) :: nil) type_var) =>
            apply (IHn theta T V X t P)
      end;
        repeat step || autorewrite with bsize in * ||
               apply reducible_unused2 || t_fv_open || t_listutils ||
               finisher || apply is_erased_type_topen;
          try omega;
          eauto with bapply_any.

       match goal with
       | H: _ |- _ => apply reducible_unused3 in H
       end; repeat step || finisher || apply_any.

    - exists (makeFresh ((X0 :: nil) :: (X :: nil) :: support theta :: pfv V type_var :: pfv U type_var :: pfv (psubstitute U [(X, V)] type_var) type_var :: nil)); repeat step || finisher.
      instantiate_any; eapply reduces_to_equiv; eauto 1; steps.

      lazymatch goal with
      | H: reducible_values _ _ _ |- reducible_values ((?M,?RC) :: _) _ _ =>
        apply (reducible_rename_one _ _ _ _ _ M) in H
      end; repeat step || finisher.

      lazymatch goal with
      | H: reducible_values _ _ _ |- _ =>
        rewrite substitute_topen2 in H by repeat step || finisher
      end.
      lazymatch goal with
      | IHn: forall theta U V X v P, _,
        H1: reducible_values ?theta ?t (psubstitute ?T ((?X,?V) :: nil) type_var) |-
          reducible_values ?theta ?t ?T =>
            apply (IHn theta T V X t P)
      end;
        repeat step || autorewrite with bsize in * ||
               apply reducible_unused2 || t_fv_open || t_listutils ||
               finisher || apply is_erased_type_topen;
          try omega;
          eauto with bapply_any.

       match goal with
       | H: _ |- _ => apply reducible_unused3 in H
       end; repeat step || finisher || apply_any.
Qed.

Lemma reducibility_subst:
  forall (theta: interpretation) U V X v P,
    valid_interpretation theta ->
    twf V 0 ->
    wf V 0 ->
    is_erased_type U ->
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
                         _ _ _ _ _ _) H)
  end;
    repeat tac1 || rewrite substitute_nothing3 in *;
      eauto using reducibility_is_candidate;
      try solve [ eapply reducible_unused2; steps; eauto using reducibility_is_candidate ];
      try solve [ eapply reducible_unused3 with X _; steps; eauto using reducibility_is_candidate ];
      eauto 2 with berased step_tactic.
Qed.
