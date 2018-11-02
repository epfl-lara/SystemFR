Require Import Equations.Equations.

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

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
Require Import Termination.Freshness.
Require Import Termination.Equivalence.
Require Import Termination.EquivalentWithRelation.
Require Import Termination.SetLemmas.
Require Import Termination.IdRelation.

Require Import Termination.FVLemmas.
Require Import Termination.FVLemmasLists.

Require Import Termination.RedTactics.
Require Import Termination.ReducibilityCandidate.
Require Import Termination.ReducibilityDefinition.
Require Import Termination.ReducibilityLemmas.

Require Import PeanoNat.

Require Import Omega.

Open Scope list_scope.

Opaque reducible_values.
Opaque makeFresh.

Lemma reduces_to_equiv:
  forall (P P': tree -> Prop) t,
    reduces_to P t ->
    (forall v, P v -> P' v) ->
    reduces_to P' t.
Proof.
  unfold reduces_to; repeat step || eexists; eauto.
Qed.

Lemma erased_is_erased:
  forall (t: erased_term), is_erased_term t.
Proof.
  destruct t; auto.
Qed.

Hint Resolve erased_is_erased: berased.

Lemma erased_term_tfv:
  forall (t: erased_term), pfv t type_var = nil.
Proof.
  destruct t; steps; eauto using is_erased_term_tfv.
Qed.

Lemma is_erased_subst:
  forall t l,
    is_erased_term t ->
    psubstitute t l type_var = t.
Proof.
  intros; rewrite substitute_nothing5; eauto with bfv.
Qed.

Lemma equal_with_relation_refl:
  forall t rel,
    pfv t type_var = nil ->
    equal_with_relation rel t t.
Proof.
  induction t; repeat step || t_listutils;
   try solve [ unfold singleton in *; unfold add in *; steps ].
Qed.

Lemma equal_with_relation_topen:
  forall t1 t2 x y rel k,
    (x ∈ pfv t1 type_var -> False) ->
    (y ∈ pfv t2 type_var -> False) ->
    equal_with_relation rel t1 t2 ->
    equal_with_relation ((x,y) :: rel)
                        (topen k t1 (fvar x type_var))
                        (topen k t2 (fvar y type_var)).
Proof.
  induction t1; destruct t2; intros; try destruct_tag;
    simpl in *; intuition auto;
      try solve [ repeat step || t_listutils ].
Qed.

Lemma equal_with_relation_open:
  forall t1 t2 a rel k,
    pfv a type_var = nil ->
    equal_with_relation rel t1 t2 ->
    equal_with_relation rel (open k t1 a) (open k t2 a).
Proof.
  induction t1; destruct t2; intros; try destruct_tag; simpl in *; intuition auto; steps;
    eauto using equal_with_relation_refl.
Qed.

Lemma equivalent_with_relation_add:
  forall T (l1 l2: list (nat * T)) x y t rel,
    equivalent_with_relation rel l1 l2 ->
    equivalent_with_relation ((x,y) :: rel) ((x,t) :: l1) ((y,t) :: l2).
Proof.
  unfold equivalent_with_relation;
    repeat step || t_lookup;
    try solve [ eapply_any; eauto; steps ].
Qed.

Ltac t_instantiate_rel :=
  match goal with
  | H1: equivalent_with_relation ?rel ?theta ?theta',
    H2: lookup _ ?rel ?x = Some ?y,
    H3: lookup _ (swap ?rel) ?y = Some ?x,
    H4: lookup _ ?theta ?x = Some ?t |- _ =>
      poseNew (Mark (x,y,t) "equivalent_with_relation");
      pose proof (H1 x y t H2 H3)
  | H1: equivalent_with_relation ?rel ?theta ?theta',
    H2: lookup _ ?rel ?x = Some ?y,
    H3: lookup _ (swap ?rel) ?y = Some ?x,
    H4: lookup _ ?theta' ?y = Some ?t |- _ =>
      poseNew (Mark (x,y,t) "equivalent_with_relation");
      pose proof (H1 x y t H2 H3)
  end.

Lemma equal_with_relation_size:
  forall t1 t2 rel,
    equal_with_relation rel t1 t2 ->
    size t1 = size t2.
Proof.
  induction t1;
    repeat match goal with
           | _ => step
           | H: _ |- _ => erewrite H; eauto
           end.
Qed.

Set Program Mode.

Lemma reducible_rename_aux:
  forall n T T' t (theta theta' : interpretation) rel,
    size T < n ->
    valid_interpretation theta ->
    valid_interpretation theta' ->
    equivalent_with_relation rel theta theta' ->
    equal_with_relation rel T T' ->
    (
      reducible_values theta t T <->
      reducible_values theta' t T'
    ).
Proof.
  induction n; eauto with omega;
    destruct T;
      repeat match goal with
      | _ => step || t_fv_open ||  simp_red || t_listutils || t_lookup || destruct_tag || finisher
      | _ => apply equal_with_relation_open
      | _ => t_instantiate_rel
      | _ => t_equal_with_erased
      | H: is_erased_term ?t |- _ => rewrite (is_erased_subst t) in *
      | _ => apply erased_is_erased
      | _ => rewrite erased_term_tfv in *
      | _ => progress ( autorewrite with bsize in * )
      | _ => rewrite substitute_open2 in * by
            (repeat step || ( rewrite erased_term_tfv in * ) ||
                    eauto using is_renaming_twfs, is_renaming_wfs)
      | IHn: forall T T' t theta theta' l, _ ,
        H1: reducible_values ?theta' ?t ?T',
        H2: equal_with_relation ?rel ?T ?T' |-
          reducible_values ?theta ?t ?T =>
            apply (IHn T T' t theta theta' rel)
      | IHn: forall T T' t theta theta' l, _ ,
        H1: reducible_values ?theta ?t ?T,
        H2: equal_with_relation ?rel ?T ?T' |-
          reducible_values ?theta' ?t ?T' =>
            apply (IHn T T' t theta theta' rel)
      | IHn: forall T T' t theta theta' l, _ ,
        H1: reducible_values ?theta' ?t (open 0 ?T' ?a) ,
        H2: equal_with_relation ?rel ?T ?T' |-
          reducible_values ?theta ?t (open 0 ?T ?a) =>
            apply (IHn (open 0 T a) (open 0 T' a) t theta theta' rel)
      | IHn: forall T T' t theta theta' l, _ ,
        H1: reducible_values ?theta ?t (open 0 ?T ?a),
        H2: equal_with_relation ?rel ?T ?T' |-
          reducible_values ?theta' ?t (open 0 ?T' ?a) =>
            apply (IHn (open 0 T a) (open 0 T' a) t theta theta' rel)
      | b: erased_term, H: forall a, _ -> reduces_to (fun t => reducible_values ?theta t (open 0 ?T _)) _ |-
          reduces_to _ _ =>
        poseNew (Mark 0 "reduces_to_equiv");
        apply reduces_to_equiv with (fun t => reducible_values theta t (open 0 T b))
      | |- _ ∈ support _ => apply_any
      | H: forall a, _ -> reduces_to _ _ |- _ => apply H
      | H: forall a, _ -> reducible_values _ _ _ |- _ => apply H
      | H1: forall a, reducible_values _ _ _ -> _,
        a: erased_term  |- _ =>
          poseNew (Mark H1 "instantiate");
          unshelve epose proof (H1 a _)
      | |- exists c d, pp ?a ?b = pp _ _ /\ _ => unshelve exists a, b
      | H: star small_step _ ?a |- _ => unshelve exists a
      | a: erased_term |- _ => unshelve exists a
      | H1: equal_with_relation _ ?T ?T',
        H: reducible_values _ ?t ?T |- reducible_values _ ?t ?T' \/ _ => left
      | H1: equal_with_relation _ ?T' ?T,
        H: reducible_values _ ?t ?T |- reducible_values _ ?t ?T' \/ _ => left
      | H1: equal_with_relation _ ?T ?T',
        H: reducible_values _ ?t ?T |- _ \/ reducible_values _ ?t ?T' => right
      | H1: equal_with_relation _ ?T' ?T,
        H: reducible_values _ ?t ?T |- _ \/ reducible_values _ ?t ?T' => right
      | H1: equal_with_relation ?rel ?T ?T' |- exists X, (X ∈ ?L -> False) /\ _ =>
          exists (makeFresh (L :: (range rel) :: (range (swap rel)) :: (pfv T type_var) :: (pfv T' type_var) :: nil))
      end;
      try omega;
      eauto with falsity;
      eauto with bwf.

     - instantiate_any. eapply reduces_to_equiv; eauto 1; steps.
      lazymatch goal with
      | IHn: forall T T' t theta theta' rel, _ ,
        H1: reducible_values ((?X,?RC) :: ?theta) ?t ?T,
        H2: equal_with_relation ?rel _ _ |-
          reducible_values ((?M,?RC) :: ?theta') ?t ?T' =>
            unshelve epose proof
              (IHn T T' t
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
          apply nodup_remove_support ||
          apply nodup_remove_support_range ||
          (rewrite substitute_topen3 in * by steps);
        try omega;
        eauto using in_remove_support.

    - instantiate_any. eapply reduces_to_equiv; eauto 1; steps.
      lazymatch goal with
      | IHn: forall T T' t theta theta' rel, _ ,
        H1: reducible_values ((?X,?RC) :: ?theta) ?t ?T,
        H2: equal_with_relation ?rel _ _ |-
          reducible_values ((?M,?RC) :: ?theta') ?t ?T' =>
            unshelve epose proof
              (IHn T T' t
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
          apply nodup_remove_support ||
          apply nodup_remove_support_range ||
          match goal with
          | H: equal_with_relation _ _ _ |- _ =>
            rewrite (equal_with_relation_size _ _ _ H) in * by steps
          end ||
          (rewrite substitute_topen3 in * by steps);
        try omega;
        eauto using in_remove_support.
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

Ltac t_idrel :=
  rewrite support_idrel in * ||
  rewrite support_swap in * ||
  rewrite range_idrel in * ||
  rewrite range_swap in * ||
  (rewrite idrel_lookup in * by auto) ||
  (rewrite idrel_lookup_swap_fail in * by auto).

Lemma reducible_rename_one:
  forall RC theta v T X Y,
    valid_interpretation theta ->
    reducibility_candidate RC ->
    (X ∈ pfv T type_var -> False) ->
    (Y ∈ pfv T type_var -> False) ->
    reducible_values ((X,RC) :: theta) v (topen 0 T (fvar X type_var)) ->
    reducible_values ((Y,RC) :: theta) v (topen 0 T (fvar Y type_var)).
Proof.
  intros.
  eapply (reducible_rename _ _ _ _ _ ((X,Y) :: idrel (pfv T type_var))); eauto;
    repeat step || t_idrel || t_lookup ||
           apply equivalent_with_relation_add ||
           apply equal_with_relation_topen ||
           apply equal_with_idrel ||
           unfold equivalent_with_relation.
Qed.
