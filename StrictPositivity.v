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

Require Import Termination.FVLemmas.

Opaque makeFresh.
Opaque Nat.eq_dec.
Opaque reducible_values.

Definition no_type_fvar T vars :=
  forall X, X ∈ pfv T type_var -> X ∈ vars -> False.

Equations strictly_positive (T: tree) (vars: list nat): Prop
    by wf (size T) lt :=
  strictly_positive (fvar _ type_var) _ := True;
  strictly_positive (lvar _ _) _ := True;

  strictly_positive T_unit _ := True;
  strictly_positive T_bool _ := True;
  strictly_positive T_nat _ := True;
  strictly_positive T_top _ := True;
  strictly_positive T_bot _ := True;
  strictly_positive (T_equal _ _) _ := True;

  strictly_positive (T_prod T1 T2) vars := strictly_positive T1 vars /\ strictly_positive T2 vars;
  strictly_positive (T_arrow T1 T2) vars := no_type_fvar T1 vars /\ strictly_positive T2 vars;
  strictly_positive (T_forall T1 T2) vars := no_type_fvar T1 vars /\ strictly_positive T2 vars;
  strictly_positive (T_sum T1 T2) vars := strictly_positive T1 vars /\ strictly_positive T2 vars;
  strictly_positive (T_refine T p) vars := strictly_positive T vars;
  strictly_positive (T_let t T1 T2) vars :=
    strictly_positive T1 vars /\ strictly_positive T2 vars;
  strictly_positive (T_singleton _) _ := True;
  strictly_positive (T_intersection T1 T2) _ :=
    strictly_positive T1 vars /\ strictly_positive T2 vars;

  (* could be relaxed *)
  strictly_positive (T_union T1 T2) vars :=
    no_type_fvar T1 vars /\ no_type_fvar T2 vars;
  strictly_positive (T_exists T1 T2) vars := no_type_fvar T1 vars /\ no_type_fvar T2 vars;

  strictly_positive (T_abs T) vars := strictly_positive T vars;
  strictly_positive (T_rec n T0 Ts) vars :=
    strictly_positive T0 vars /\ strictly_positive Ts vars /\ (
      (no_type_fvar T0 vars /\ no_type_fvar Ts vars) \/
      exists X,
        ~(X ∈ pfv Ts type_var) /\
        strictly_positive (topen 0 Ts (fvar X type_var)) (X :: nil)
    );

  strictly_positive _ vars := False.


Solve All Obligations with (repeat step || autorewrite with bsize in *; try omega; eauto with omega).
Fail Next Obligation.

Ltac simp_spos :=
  rewrite strictly_positive_equation_1 in * ||
  rewrite strictly_positive_equation_2 in * ||
  rewrite strictly_positive_equation_3 in * ||
  rewrite strictly_positive_equation_4 in * ||
  rewrite strictly_positive_equation_5 in * ||
  rewrite strictly_positive_equation_6 in * ||
  rewrite strictly_positive_equation_7 in * ||
  rewrite strictly_positive_equation_8 in * ||
  rewrite strictly_positive_equation_9 in * ||
  rewrite strictly_positive_equation_10 in * ||
  rewrite strictly_positive_equation_11 in * ||
  rewrite strictly_positive_equation_12 in * ||
  rewrite strictly_positive_equation_13 in * ||
  rewrite strictly_positive_equation_14 in * ||
  rewrite strictly_positive_equation_15 in * ||
  rewrite strictly_positive_equation_16 in * ||
  rewrite strictly_positive_equation_17 in * ||
  rewrite strictly_positive_equation_18 in * ||
  rewrite strictly_positive_equation_19 in * ||
  rewrite strictly_positive_equation_20 in * ||
  rewrite strictly_positive_equation_21 in * ||
  rewrite strictly_positive_equation_22 in * ||
  rewrite strictly_positive_equation_23 in * ||
  rewrite strictly_positive_equation_24 in * ||
  rewrite strictly_positive_equation_25 in * ||
  rewrite strictly_positive_equation_26 in * ||
  rewrite strictly_positive_equation_27 in * ||
  rewrite strictly_positive_equation_28 in * ||
  rewrite strictly_positive_equation_29 in * ||
  rewrite strictly_positive_equation_30 in * ||
  rewrite strictly_positive_equation_31 in * ||
  rewrite strictly_positive_equation_32 in * ||
  rewrite strictly_positive_equation_33 in * ||
  rewrite strictly_positive_equation_34 in * ||
  rewrite strictly_positive_equation_35 in * ||
  rewrite strictly_positive_equation_36 in * ||
  rewrite strictly_positive_equation_37 in * ||
  rewrite strictly_positive_equation_38 in * ||
  rewrite strictly_positive_equation_39 in * ||
  rewrite strictly_positive_equation_40 in * ||
  rewrite strictly_positive_equation_41 in * ||
  rewrite strictly_positive_equation_42 in * ||
  rewrite strictly_positive_equation_43 in * ||
  rewrite strictly_positive_equation_44 in * ||
  rewrite strictly_positive_equation_45 in * ||
  rewrite strictly_positive_equation_46 in * ||
  rewrite strictly_positive_equation_47 in * ||
  rewrite strictly_positive_equation_48 in * ||
  rewrite strictly_positive_equation_49 in * ||
  rewrite strictly_positive_equation_50 in *.

Opaque strictly_positive.

Lemma is_erased_term_no_type_fvar:
  forall t vars,
    is_erased_term t ->
    no_type_fvar t vars.
Proof.
  unfold no_type_fvar; repeat step || rewrite is_erased_term_tfv in *.
Qed.

Lemma no_type_fvar_open:
  forall T vars rep k,
    is_erased_term rep ->
    no_type_fvar T vars ->
    no_type_fvar (open k T rep) vars.
Proof.
  unfold no_type_fvar;
    repeat step || t_fv_open || t_listutils ||
           rewrite is_erased_term_tfv in * by steps; eauto.
Qed.

Definition non_empty theta A := exists v, reducible_values theta v A.

Lemma instantiate_non_empty:
  forall theta (A: tree) (P: tree -> Prop),
    non_empty theta A ->
    (forall a, reducible_values theta a A -> P a) ->
    exists a, reducible_values theta a A /\ P a.
Proof.
  unfold non_empty; steps; eauto.
Qed.

Ltac t_instantiate_non_empty :=
  match goal with
  | H1: non_empty ?theta ?A, H2: forall a, reducible_values ?theta a ?A -> _ |- _ =>
    pose proof (instantiate_non_empty _ _ _ H1 H2)
  end.

Lemma non_empty_extend:
  forall theta A x RC,
    non_empty theta A ->
    reducibility_candidate RC ->
    valid_interpretation theta ->
    ~(x ∈ pfv A type_var) ->
    non_empty ((x, RC) :: theta) A.
Proof.
  unfold non_empty; repeat step || exists v || apply reducible_unused2.
Qed.

Definition push_one (a: tree) (l: list (nat * (tree -> tree -> Prop))): interpretation :=
  mapValues (fun rc => rc a) l.

Definition push_all (P: tree -> Prop) (l: list (nat * (tree -> tree -> Prop))): interpretation :=
  mapValues (fun (rc: tree -> tree -> Prop) (v: tree) => (forall a, P a -> rc a v)) l.

Fixpoint valid_pre_interpretation (P: tree -> Prop) (theta: list (nat * (tree -> tree -> Prop))) : Prop :=
  match theta with
  | nil => True
  | (_, RC) :: theta' => valid_pre_interpretation P theta' /\ forall a, P a -> reducibility_candidate (RC a)
  end.

Lemma valid_interpretation_one:
  forall a (P: tree -> Prop) theta,
    P a ->
    valid_pre_interpretation P theta ->
    valid_interpretation (push_one a theta).
Proof.
  induction theta; steps.
Qed.

Definition sat { X } (P: X -> Prop) := exists x, P x.

Lemma valid_interpretation_all:
  forall (P: tree -> Prop) theta,
    sat P ->
    valid_pre_interpretation P theta ->
    valid_interpretation (push_all P theta).
Proof.
  unfold sat; induction theta;
    repeat step || unfold reducibility_candidate in * || instantiate_any.
Qed.

Lemma valid_interpretation_append:
  forall theta1 theta2,
    valid_interpretation theta1 ->
    valid_interpretation theta2 ->
    valid_interpretation (theta1 ++ theta2).
Proof.
  induction theta1; steps.
Qed.

Lemma valid_interpretation_all2:
  forall theta theta' A,
    non_empty theta A ->
    valid_interpretation theta ->
    valid_pre_interpretation (fun a => reducible_values theta a A) theta' ->
    valid_interpretation (push_all (fun a => reducible_values theta a A) theta' ++ theta).
Proof.
  repeat step || apply valid_interpretation_append || apply valid_interpretation_all || unfold sat.
Qed.

Hint Resolve valid_interpretation_cons: b_valid_interp.
Hint Resolve valid_interpretation_one: b_valid_interp.
Hint Resolve valid_interpretation_all: b_valid_interp.
Hint Resolve valid_interpretation_all2: b_valid_interp.
Hint Resolve valid_interpretation_append: b_valid_interp.
Hint Extern 1 => eapply valid_interpretation_one; eauto: b_valid_interp.

Ltac t_reducible_unused3 :=
  match goal with
  | H: reducible_values ((?X,?RC) :: ?theta) ?v ?T |- reducible_values ?theta' ?v ?T =>
    unify theta theta'; apply reducible_unused3 with X RC
  end.

Lemma no_type_fvar_tail:
  forall T x xs,
    no_type_fvar T (x :: xs) ->
    no_type_fvar T xs.
Proof.
  unfold no_type_fvar; repeat step; eauto.
Qed.

Lemma no_type_fvar_head:
  forall T x xs,
    no_type_fvar T (x :: xs) ->
    x ∈ pfv T type_var ->
    False.
Proof.
  unfold no_type_fvar; repeat step; eauto.
Qed.

Hint Immediate no_type_fvar_head: b_no_type_fvar.
Hint Resolve no_type_fvar_tail: b_no_type_fvar.

Lemma reducible_unused_push_all1:
  forall theta' P theta T v,
    sat P ->
    no_type_fvar T (support theta') ->
    valid_pre_interpretation P theta' ->
    valid_interpretation theta ->
    reducible_values (push_all P theta' ++ theta) v T ->
    reducible_values theta v T.
Proof.
  induction theta';
    repeat step || (poseNew (Mark 0 "once"); eapply IHtheta') || t_reducible_unused3 ||
           apply valid_interpretation_append || apply valid_interpretation_all || unfold sat in * ||
           unfold reducibility_candidate in * || instantiate_any;
    eauto with b_no_type_fvar.
Qed.

Lemma reducible_unused_push_all2:
  forall theta' P theta T v,
    sat P ->
    no_type_fvar T (support theta') ->
    valid_pre_interpretation P theta' ->
    valid_interpretation theta ->
    reducible_values theta v T ->
    reducible_values (push_all P theta' ++ theta) v T.
Proof.
  induction theta';
    repeat step || (poseNew (Mark 0 "once"); eapply IHtheta') || apply reducible_unused2 ||
           apply valid_interpretation_append || apply valid_interpretation_all || unfold sat in * ||
           unfold reducibility_candidate in * || instantiate_any;
    eauto with b_no_type_fvar.
Qed.

Lemma reducible_unused_push_all:
  forall theta' P theta T v,
    sat P ->
    no_type_fvar T (support theta') ->
    valid_pre_interpretation P theta' ->
    valid_interpretation theta -> (
      reducible_values (push_all P theta' ++ theta) v T <->
      reducible_values theta v T
    ).
Proof.
  intuition auto; eauto using reducible_unused_push_all1, reducible_unused_push_all2.
Qed.

Lemma reducible_unused_push_one1:
  forall theta' (P: tree -> Prop) a theta T v,
    no_type_fvar T (support theta') ->
    P a ->
    valid_pre_interpretation P theta' ->
    valid_interpretation theta ->
    reducible_values (push_one a theta' ++ theta) v T ->
    reducible_values theta v T.
Proof.
  induction theta';
    repeat step || (poseNew (Mark 0 "once"); eapply IHtheta') || t_reducible_unused3 ||
           apply valid_interpretation_append || eapply valid_interpretation_one || unfold sat in * ||
           unfold reducibility_candidate in * || instantiate_any;
    eauto with b_no_type_fvar.
Qed.

Lemma reducible_unused_push_one2:
  forall theta' (P: tree -> Prop) theta T v a,
    P a ->
    no_type_fvar T (support theta') ->
    valid_pre_interpretation P theta' ->
    valid_interpretation theta ->
    reducible_values theta v T ->
    reducible_values (push_one a theta' ++ theta) v T.
Proof.
  induction theta';
    repeat step || apply reducible_unused2 || apply valid_interpretation_append ||
           (eapply valid_interpretation_one; eauto);
    eauto with b_no_type_fvar;
    try solve [ eapply IHtheta'; eauto with b_no_type_fvar ].
Qed.

Lemma reducible_unused_push_one:
  forall theta' (P: tree -> Prop) theta T a v,
    P a ->
    no_type_fvar T (support theta') ->
    valid_pre_interpretation P theta' ->
    valid_interpretation theta -> (
      reducible_values (push_one a theta' ++ theta) v T <->
      reducible_values theta v T
    ).
Proof.
  intuition auto; eauto using reducible_unused_push_one1, reducible_unused_push_one2.
Qed.

Lemma valid_pre_interpretation_same:
  forall P1 P2 theta,
    valid_pre_interpretation P1 theta ->
    (forall a, P1 a <-> P2 a) ->
    valid_pre_interpretation P2 theta.
Proof.
  induction theta; steps; eauto with bapply_any.
Qed.

Ltac t_valid_pre_interpration_same :=
  match goal with
  | H: valid_pre_interpretation ?P1 ?theta |- valid_pre_interpretation ?P2 ?theta =>
     apply valid_pre_interpretation_same with P1
  end.

Ltac t_instantiate_reducible2 :=
  match goal with
  | H0: no_type_fvar ?T (support ?theta'),
    H1:reducible_values _ ?v ?T,
    H2:is_erased_term ?v,
    H3: forall a, _ -> reducible_values (push_one _ ?theta' ++ ?theta) a ?T -> _
    |- _ => poseNew (Mark (v, H3) "t_instantiate_reducible2");
          unshelve epose proof (H3 v H2 _)
  end.

Ltac t_rewrite_push_one :=
  match goal with
  | H1: reducible_values ?theta ?a ?A,
    H2: reducible_values (push_one ?a ?theta' ++ ?theta) ?v ?T |- _ =>
      rewrite (reducible_unused_push_one _ (fun a => reducible_values theta a A)) in H2 by (
        (repeat step || apply no_type_fvar_open || t_valid_pre_interpration_same);
        try solve [ apply_any; assumption ]
      )
  | H1: reducible_values ?theta ?a ?A |-
        reducible_values (push_one ?a ?theta' ++ ?theta) ?v ?T =>
      rewrite (reducible_unused_push_one _ (fun a => reducible_values theta a A)) by (
        (repeat step || apply no_type_fvar_open || t_valid_pre_interpration_same);
        try solve [ apply_any; assumption ]
      )
  end.

Lemma strictly_positive_open_aux:
  forall n T vars rep k,
    size T < n ->
    is_erased_type T ->
    is_erased_term rep ->
    strictly_positive T vars ->
    strictly_positive (open k T rep) vars.
Proof.
  induction n; destruct T; repeat step || simp_spos || apply no_type_fvar_open || apply IHn ;
    try omega;
    try solve [ left; repeat step || apply no_type_fvar_open ];
    try solve [ right; eexists; eauto; repeat step || apply no_type_fvar_open ].

  right. exists X; repeat step || t_fv_open || t_listutils || rewrite is_erased_term_tfv in * by steps.
  rewrite <- open_topen;
    repeat step || apply IHn || autorewrite with bsize in * || apply is_erased_type_topen;
    eauto with btwf bwf omega.
Qed.

Lemma strictly_positive_open:
  forall T vars rep k,
    is_erased_type T ->
    is_erased_term rep ->
    strictly_positive T vars ->
    strictly_positive (open k T rep) vars.
Proof.
  eauto using strictly_positive_open_aux.
Qed.

Lemma push_all_cons:
  forall X (RC: tree -> Prop) theta (P: tree -> Prop),
    (X, fun v => forall a, P a -> RC v) :: push_all P theta = push_all P ((X, fun a => RC) :: theta).
Proof.
  steps.
Qed.

Lemma push_is_candidate:
  forall (theta : interpretation) (A a : tree) (RC : tree -> Prop),
    reducibility_candidate RC ->
    reducible_values theta a A ->
    reducibility_candidate (fun v : tree => reducible_values theta a A -> RC v).
Proof.
  repeat step || unfold non_empty in * || unfold reducibility_candidate in * || instantiate_any;
    eauto with bfv bwf.
Qed.

Lemma push_all_is_candidate:
  forall (theta : interpretation) (A : tree) (RC : tree -> Prop),
    reducibility_candidate RC ->
    non_empty theta A ->
    reducibility_candidate (fun v : tree => forall a, reducible_values theta a A -> RC v).
Proof.
  repeat step || unfold non_empty in * || unfold reducibility_candidate in * || instantiate_any;
    eauto with bfv bwf.
Qed.

Ltac find_exists2 :=
  match goal with
  | H1: reducible_values ?theta ?a ?T1,
    H2: reducible_values ?theta ?v (open 0 ?T2 ?a)
    |- _ =>
    exists a
  end.

Lemma no_type_fvar_strictly_positive:
  forall T vars,
    is_erased_type T ->
    no_type_fvar T vars ->
    strictly_positive T vars.
Proof.
  induction T; repeat step || simp_spos || destruct_tag || unfold no_type_fvar in * || apply_any || left;
    try solve [ eapply_any; eauto; repeat step || t_listutils ].
Qed.

Ltac t_red_is_val :=
  eapply red_is_val; eauto;
    repeat step || apply valid_interpretation_append || eapply valid_interpretation_one ||
    eauto with b_valid_interp; steps;
    eauto with bapply_any.

Hint Extern 50 => solve [ t_red_is_val ]: b_red_is_val.

Lemma sat_p:
  forall P theta a A,
    reducible_values theta a A ->
    (forall a, P a <-> reducible_values theta a A) ->
    sat P.
Proof.
  unfold sat; steps; eauto with bapply_any.
Qed.

Lemma no_type_fvar_in_topen:
  forall T vars k X,
    no_type_fvar T vars ->
    ~(X ∈ vars) ->
    no_type_fvar (topen k T (fvar X type_var)) vars.
Proof.
  unfold no_type_fvar; repeat step || t_fv_open || t_listutils; eauto.
Qed.

Definition similar_sets (rel: M nat nat) (vars vars': list nat): Prop :=
  forall x y,
    lookup Nat.eq_dec rel x = Some y ->
    lookup Nat.eq_dec (swap rel) y = Some x ->
    (x ∈ vars <-> y ∈ vars').

Opaque strictly_positive.

Lemma equal_with_relation_pfv:
  forall T T' rel X,
    equal_with_relation rel T T' ->
    X ∈ pfv T type_var ->
    exists X',
      X' ∈ pfv T' type_var /\
      lookup Nat.eq_dec rel X = Some X' /\
      lookup Nat.eq_dec (swap rel) X' = Some X.
Proof.
  induction T;
    repeat match goal with
           | H1: equal_with_relation ?rel ?T ?T',
             H2: ?X ∈ pfv ?T type_var,
             H3: forall _ _ _, _ -> _ -> _ |- _ => pose proof (H3 _ _ _ H1 H2); clear H3
           | _ => step || t_listutils || destruct_tag
           end; eauto;
      try solve [ eexists; repeat step || t_listutils; eauto ].
Qed.

Ltac t_equal_with_relation_pfv :=
  match goal with
  | H1: equal_with_relation ?rel ?T ?T',
    H2: ?X ∈ pfv ?T type_var |- _ =>
    poseNew (Mark H1 "equal_with_relation_pfv");
    pose proof (equal_with_relation_pfv _ _ _ _ H1 H2)
  end.

Lemma equal_with_relation_pfv2:
  forall T T' rel X',
    equal_with_relation rel T T' ->
    X' ∈ pfv T' type_var ->
    exists X,
      X ∈ pfv T type_var /\
      lookup Nat.eq_dec rel X = Some X' /\
      lookup Nat.eq_dec (swap rel) X' = Some X.
Proof.
  intros.
  apply equal_with_relation_swap in H.
  repeat step || t_equal_with_relation_pfv || eexists || rewrite swap_twice in *; eauto.
Qed.

Ltac t_equal_with_relation_pfv2 :=
  match goal with
  | H1: equal_with_relation ?rel ?T ?T',
    H2: ?X ∈ pfv ?T' type_var |- _ =>
    poseNew (Mark H1 "equal_with_relation_pfv2");
    pose proof (equal_with_relation_pfv2 _ _ _ _ H1 H2)
  | _ => t_equal_with_relation_pfv
  end.

Lemma no_type_fvar_rename:
  forall T T' vars vars' rel,
    no_type_fvar T vars ->
    equal_with_relation rel T T' ->
    similar_sets rel vars vars' ->
    no_type_fvar T' vars'.
Proof.
  unfold no_type_fvar, similar_sets;
    repeat step || t_equal_with_relation_pfv2 || t_lookup_same;
    eauto with beapply_any.
Qed.

Lemma strictly_positive_rename_aux:
  forall n T T' vars vars' rel,
    size T < n ->
    strictly_positive T vars ->
    equal_with_relation rel T T' ->
    similar_sets rel vars vars' ->
    strictly_positive T' vars'.
Proof.
  induction n; destruct T;
    repeat (intuition auto) || cbn -[equal_with_relation] in * || simp_spos || destruct_tag; try omega;
    match goal with
    | H: equal_with_relation  _ _ ?T |- _ => is_var T; destruct T; simpl in H
    end;
    repeat match goal with
           | H1: equal_with_relation ?rel ?T ?T',
             H2: strictly_positive ?T ?vars |-
               strictly_positive ?T' ?vars' =>
             apply IHn with T vars rel
           | _ => step || destruct_tag || simp_spos
           end;
    try omega;
    eauto using no_type_fvar_rename.

  right.
  exists (makeFresh ((X :: nil) :: pfv T'3 type_var :: nil));
    repeat step; try finisher.

  match goal with
  | H1: equal_with_relation ?rel _ _,
    H2: strictly_positive ?T (?X :: nil) |-
      strictly_positive (topen 0 ?T' (fvar ?M type_var)) ?vars' =>
    apply IHn with T (X :: nil) ((X,M) :: rel)
  end;
    repeat unfold similar_sets || step || autorewrite with bsize in * || apply equal_with_relation_topen;
      try omega;
      try finisher.
Qed.

Lemma strictly_positive_rename:
  forall T T' vars vars' rel,
    strictly_positive T vars ->
    equal_with_relation rel T T' ->
    similar_sets rel vars vars' ->
    strictly_positive T' vars'.
Proof.
  eauto using strictly_positive_rename_aux.
Qed.

Lemma topen_swap:
  forall T i j rep,
    twf rep 0 ->
    topen i (swap_type_holes T j i) rep =
    swap_type_holes (topen j T rep) j i.
Proof.
  induction T; repeat step || tequality || rewrite (swap_nothing _ 0);
    try omega.
Qed.

Lemma pfv_swap:
  forall T i j tag, pfv (swap_type_holes T i j) tag = pfv T tag.
Proof.
  induction T; steps.
Qed.

Lemma no_type_fvar_swap:
  forall T vars i j,
    no_type_fvar T vars ->
    no_type_fvar (swap_type_holes T i j) vars.
Proof.
  unfold no_type_fvar; repeat step || rewrite pfv_swap in *; eauto.
Qed.

Lemma topen_swap2:
  forall T k i j rep,
    twf rep 0 ->
    k <> i ->
    k <> j ->
    topen k (swap_type_holes T j i) rep =
    swap_type_holes (topen k T rep) j i.
Proof.
  induction T; repeat step || tequality || rewrite (swap_nothing _ 0);
    try omega.
Qed.

Lemma strictly_positive_swap_aux:
  forall n T vars i j,
    size T < n ->
    strictly_positive T vars ->
    strictly_positive (swap_type_holes T i j) vars.
Proof.
  induction n; destruct T; repeat step || simp_spos || apply_any;
    try omega;
    eauto using no_type_fvar_swap.
  right; exists X; repeat step || rewrite pfv_swap in *.
  rewrite topen_swap2; steps.
  apply IHn; repeat step || autorewrite with bsize in *; try omega.
Qed.

Lemma strictly_positive_swap:
  forall T vars i j,
    strictly_positive T vars ->
    strictly_positive (swap_type_holes T i j) vars.
Proof.
  eauto using strictly_positive_swap_aux.
Qed.

Lemma strictly_positive_topen_aux:
  forall n T vars k X,
    size T < n ->
    strictly_positive T vars ->
    ~(X ∈ vars) ->
    strictly_positive (topen k T (fvar X type_var)) vars.
Proof.
  induction n; destruct T; repeat step || simp_spos || apply IHn;
    eauto using no_type_fvar_in_topen;
    try omega.
  right; exists (makeFresh ((X0 :: nil) :: (X :: nil) :: pfv T3 type_var :: pfv (topen (S k) T3 (fvar X type_var)) type_var :: nil)); steps; try finisher.

  rewrite open_swap; repeat step.
  apply IHn; repeat step || autorewrite with bsize in *;
    try omega;
    try finisher.
  rewrite topen_swap; steps.
  apply strictly_positive_swap.
  match goal with
  | H2: strictly_positive (topen 0 ?T (fvar ?X type_var)) (?X :: nil) |-
      strictly_positive (topen 0 ?T (fvar ?M type_var)) (?M :: nil) =>
    apply strictly_positive_rename with (topen 0 T (fvar X type_var)) (X :: nil) ((X,M) :: idrel (pfv T type_var))
  end;
    unfold similar_sets;
    repeat step || apply equal_with_relation_topen;
    try finisher;
    eauto using equal_with_relation_refl2;
    eauto using equal_with_idrel.
Qed.

Lemma equivalent_with_relation_permute2:
  forall theta1 theta2 (RC : tree -> Prop) X Y l,
    ~(X ∈ support theta1) ->
    equivalent_with_relation
      ((Y, X) :: idrel l)
        ((Y, RC) :: theta1 ++ theta2)
        (theta1 ++ (X, RC) :: theta2).
Proof.
  unfold equivalent_with_relation, equivalent_rc_at;
    repeat match goal with
           | |- exists r, Some ?R = Some r /\ _ => exists R
           | |- exists r, _ /\ equivalent_rc r ?R => exists R
           | H: _ |- _ => rewrite lookup_remove2 in H by steps
           | _ => rewrite lookup_remove2 by steps
           | _ => step || t_lookup_rewrite || t_idrel || t_lookup || t_listutils ||
                 rewrite obvious_lookup in * by steps ||
                 t_lookupor || t_lookup_same
           end;
    eauto using equivalent_rc_refl.
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

  apply equivalent_with_relation_permute2; steps.
Qed.

Lemma support_push_one:
  forall theta a,
    support (push_one a theta) = support theta.
Proof.
  unfold push_one; repeat step || rewrite support_mapValues.
Qed.

Lemma support_push_all:
  forall theta P,
    support (push_all P theta) = support theta.
Proof.
  unfold push_one; repeat step || rewrite support_mapValues.
Qed.

Lemma strictly_positive_topen:
  forall T vars k X,
    strictly_positive T vars ->
    ~(X ∈ vars) ->
    strictly_positive (topen k T (fvar X type_var)) vars.
Proof.
  eauto using strictly_positive_topen_aux.
Qed.

Lemma swap_idrel:
  forall l, swap (idrel l) = idrel l.
Proof.
  induction l; steps.
Qed.

Lemma idrel_lookup2:
  forall x y l eq_dec, lookup eq_dec (idrel l) x = Some y -> x = y /\ x ∈ l.
Proof.
  induction l; repeat step || eapply_any || instantiate_any.
Qed.

Ltac t_idrel_lookup2 :=
  match goal with
  | H: lookup _ (idrel ?l) ?x = Some ?y |- _ => pose proof (idrel_lookup2 _ _ _ _ H); clear H
  end.

Lemma reducible_unused_middle:
  forall X RC theta1 theta2 v T,
    valid_interpretation theta1 ->
    valid_interpretation theta2 ->
    reducibility_candidate RC ->
    no_type_fvar T (support theta1) -> (
      reducible_values ((X,RC) :: theta1 ++ theta2) v T <->
      reducible_values ((X,RC) :: theta2) v T
    ).
Proof.
  repeat step.
  - apply reducible_rename with T ((X, RC) :: theta1 ++ theta2) (idrel (pfv T type_var));
      repeat step || apply valid_interpretation_append || (rewrite swap_idrel in * by steps) ||
             t_idrel_lookup2 || t_lookupor || t_lookup_rewrite || t_lookup ||
             unfold equivalent_with_relation, equivalent_rc_at || unfold no_type_fvar in * ||
             unshelve eauto with falsity || exact True;
      eauto using equal_with_idrel;
      eauto using equivalent_rc_refl;
    unfold equivalent_with_relation.

    exists rc2; repeat step || rewrite lookupRight || apply lookupNoneSupport; eauto using equivalent_rc_refl.
  - apply reducible_rename with T ((X, RC) :: theta2) (idrel (pfv T type_var));
      repeat step || apply valid_interpretation_append || (rewrite swap_idrel in * by steps) ||
             t_idrel_lookup2 || t_lookupor || t_lookup_rewrite || t_lookup ||
             unfold equivalent_with_relation, equivalent_rc_at || unfold no_type_fvar in * ||
             unshelve eauto with falsity || exact True;
      eauto using equal_with_idrel;
      eauto using equivalent_rc_refl;
    unfold equivalent_with_relation.

    exists rc1; repeat step || rewrite lookupRight || apply lookupNoneSupport; eauto using equivalent_rc_refl.
Qed.
