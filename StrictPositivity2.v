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
      no_type_fvar Ts vars \/
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

Lemma sat_p:
  forall P theta a A,
    reducible_values theta a A ->
    (forall a, P a <-> reducible_values theta a A) ->
    sat P.
Proof.
  unfold sat; steps; eauto with bapply_any.
Qed.

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
        apply wf_topen;
      try finisher;
      eauto with bwf btwf omega berased;
      eauto 2 using red_is_val with step_tactic;
      eauto with b_red_is_val.

Set Nested Proofs Allowed.
Lemma no_type_fvar_in_topen:
  forall T vars k X,
    no_type_fvar T vars ->
    ~(X ∈ vars) ->
    no_type_fvar (topen k T (fvar X type_var)) vars.
Proof.
  unfold no_type_fvar; repeat step || t_fv_open || t_listutils; eauto.
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
  - right; exists (makeFresh ((X0 :: nil) :: (X :: nil) :: nil)); steps.
    rewrite open_swap; repeat step.
    apply IHn; repeat step || autorewrite with bsize in *;
      try omega;
      try finisher.
    admit.
    + admit.
    + admit.
    apply IHn.
    Search (topen _ (topen _ _ _) _).

  

  
    apply reducible_unused3 in H27; steps; try finisher.

    rewrite open_swap;
      repeat step || rewrite swap_holes_twice ||
             t_instantiate_reducible || t_instantiate_rc ||
             unfold reduces_to in * || t_deterministic_star ||
             simp_red || t_reducible_rename_one || t_fv_open ||
             t_listutils ||
             unshelve eauto using valid_interpretation_cons with btwf btwf2 ||
             unshelve eauto using valid_interpretation_cons, red_is_val;
      try finisher;
      eauto using fv_in_reducible_val.

  (** Recursive type at 0 **)
  - left.
      repeat step || simp_red ||
             t_instantiate_reducible || apply_induction HH || apply left_lex ||
             t_deterministic_star ||
             t_topen_none; eauto with omega.

  (** Recursive type at n+1 **)
  - right.
      exists n'0, v'0, (makeFresh (
                       support theta ::
                       pfv A type_var ::
                       pfv n'0 type_var ::
                       pfv (topen 0 T2 (T_forall A B)) type_var ::
                       pfv (topen 1 T3 (T_forall A B)) type_var ::
                       nil));
      repeat step || simp_red ||
             t_instantiate_reducible || apply_induction HH || apply left_lex ||
             t_deterministic_star ||
             t_topen_none;
        eauto with omega;
        try finisher.

      remember (makeFresh (
                       support theta ::
                       pfv A type_var ::
                       pfv n'0 type_var ::
                       pfv (topen 0 T2 (T_forall A B)) type_var ::
                       pfv (topen 1 T3 (T_forall A B)) type_var ::
                       nil)) as M.

      apply reducibility_subst_head2;
        repeat
          step || t_listutils ||
          apply is_erased_topen ||
          apply is_erased_type_topen ||
          apply twf_topen ||
          apply wf_topen;
        try finisher;
        eauto with btwf;
        eauto with bwf.

Set Nested Proofs Allowed.
Lemma topen_rec:
  forall k n T0 Ts R,
    twf n 0 ->
    topen k (T_rec n T0 Ts) R = T_rec n (topen k T0 R) (topen (S k) Ts R).
Proof.
  repeat step || tequality || rewrite topen_none; eauto with btwf omega.
Qed.

      rewrite open_swap;
        repeat step || apply twf_topen;
        eauto with omega;
        eauto with btwf.

      rewrite <- topen_rec; eauto with btwf.
      define M2 (makeFresh (
                     pfv (swap_type_holes T3 0 1) type_var ::
                     pfv (T_rec n'0 T2 T3) type_var ::
                     nil
                )).
      rewrite (topen_twice _ _ _ M2); steps; eauto with btwf; try finisher.

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
        apply wf_topen;
      try finisher;
      eauto with bwf btwf omega berased;
      eauto 2 using red_is_val with step_tactic;
      eauto using reducibility_is_candidate.

    + admit. (* use multiset measure *)
    +

Lemma strictly_positive_close:
  forall T k1 k2 rep,
    twf rep 0 ->
    strictly_positive T k1 ->
    strictly_positive (open k2 T rep) k1.
Proof.
  induction T; steps; eauto using twf_open with btwf omega.
Qed.

      remember (makeFresh (
                       support theta ::
                       pfv A type_var ::
                       pfv n'0 type_var ::
                       pfv (topen 0 T2 (T_forall A B)) type_var ::
                       pfv (topen 1 T3 (T_forall A B)) type_var ::
                       nil)) as M.
      

     (*
    topen 0 (topen 1 A R) (topen 0 B R)
*)
(*
*)
    (*
    assert (
      topen 0 (topen 1 A (topen 0 B R)) R
      topen 0 (t_close 0 (topen 1 A (topen 0 B X)) X) R
    ).
*)
Admitted.

Lemma strictly_positive_pull_forall:
  forall T theta A B v a,
    strictly_positive T 0 ->
    wf T 0 ->
    twf T 1 ->
    wf A 0 ->
    twf A 0 ->
    wf B 1 ->
    twf B 0 ->
    valid_interpretation theta ->
    reducible_values theta a A ->
    reducible_values theta v (topen 0 T (T_forall A B)) ->
    reducible_values theta v (topen 0 T (open 0 B a)).
Proof.
(*  induction T;
    repeat t_topen_none || step ||
      simp reducible_values in * ||
      (rewrite topen_none in * by t_rewrite);
    eauto 6 with berased; eauto 11. *)
Admitted.
