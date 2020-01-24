Require Import Equations.Equations.
Require Import Equations.Prop.Subterm.

Require Import Omega.

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Export SystemFR.TOpenTClose.
Require Export SystemFR.OpenTOpen.
Require Export SystemFR.StrictPositivity.
Require Export SystemFR.NoTypeFVarLemmas.
Require Export SystemFR.ReducibilityUnused.

Opaque makeFresh.
Opaque Nat.eq_dec.
Opaque reducible_values.
Opaque strictly_positive.

Definition non_empty theta A := exists v, reducible_values theta v A.

Lemma instantiate_non_empty:
  forall theta A,
    non_empty theta A ->
    exists a, reducible_values theta a A.
Proof.
  unfold non_empty; steps; eauto.
Qed.

Ltac instantiate_non_empty :=
  match goal with
  | H: non_empty ?theta ?A |- _ =>
    poseNew (Mark (theta,A) "instantiate_non_empty");
    pose proof (instantiate_non_empty _ _ H)
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

Lemma strictly_positive_open_aux:
  forall n T vars rep k,
    type_nodes T < n ->
    is_erased_type T ->
    is_erased_term rep ->
    strictly_positive T vars ->
    strictly_positive (open k T rep) vars.
Proof.
  induction n; destruct T; repeat step || simp_spos || apply no_type_fvar_open || apply IHn ;
    try omega;
    try solve [ left; repeat step || apply no_type_fvar_open ];
    try solve [ right; eexists; eauto; repeat step || apply no_type_fvar_open ].

  right. exists X; repeat step || fv_open || list_utils || rewrite is_erased_term_tfv in * by steps.
  rewrite <- open_topen;
    repeat step || apply IHn || autorewrite with bsize in * || apply is_erased_type_topen;
    eauto with twf wf omega.
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
    eauto with fv wf.
Qed.

Lemma push_all_is_candidate:
  forall (theta : interpretation) (A : tree) (RC : tree -> Prop),
    reducibility_candidate RC ->
    non_empty theta A ->
    reducibility_candidate (fun v : tree => forall a, reducible_values theta a A -> RC v).
Proof.
  repeat step || unfold non_empty in * || unfold reducibility_candidate in * || instantiate_any;
    eauto with fv wf.
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
    try solve [ eapply_any; eauto; repeat step || list_utils ].
Qed.

Ltac t_red_is_val :=
  eapply red_is_val; eauto;
    repeat step || apply valid_interpretation_append || eapply valid_interpretation_one ||
    eauto with b_valid_interp; steps;
    eauto with apply_any.

Hint Extern 50 => solve [ t_red_is_val ]: b_red_is_val.

Lemma strictly_positive_rename_aux:
  forall n T T' vars vars' rel,
    type_nodes T < n ->
    strictly_positive T vars ->
    equal_with_relation type_var rel T T' ->
    similar_sets rel vars vars' ->
    strictly_positive T' vars'.
Proof.
  induction n;
    try solve [ intros; omega ];
    destruct T; inversion 3;
    repeat match goal with
           | _ => step || simp_spos || destruct_tag
           | H1: equal_with_relation _ ?rel ?T ?T',
             H2: strictly_positive ?T ?vars |-
               strictly_positive ?T' ?vars' =>
             apply IHn with T vars rel
            end;
    eauto using no_type_fvar_rename;
    try omega.

  right.
  exists (makeFresh ((X :: nil) :: pfv Ts' type_var :: nil));
    repeat step; try finisher.

  match goal with
  | H1: equal_with_relation _ ?rel _ _,
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
    equal_with_relation type_var rel T T' ->
    similar_sets rel vars vars' ->
    strictly_positive T' vars'.
Proof.
  eauto using strictly_positive_rename_aux.
Qed.

Lemma no_type_fvar_swap:
  forall T vars i j,
    no_type_fvar T vars ->
    no_type_fvar (swap_type_holes T i j) vars.
Proof.
  unfold no_type_fvar; repeat step || rewrite pfv_swap_type_holes in *; eauto.
Qed.

Lemma strictly_positive_swap_aux:
  forall n T vars i j,
    type_nodes T < n ->
    strictly_positive T vars ->
    strictly_positive (swap_type_holes T i j) vars.
Proof.
  induction n; destruct T; repeat step || simp_spos || apply_any;
    try omega;
    eauto using no_type_fvar_swap.
  right; exists X; repeat step || rewrite pfv_swap_type_holes in *.
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
    type_nodes T < n ->
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

Lemma support_push_one:
  forall theta a,
    support (push_one a theta) = support theta.
Proof.
  unfold push_one; repeat step || rewrite support_map_values.
Qed.

Lemma support_push_all:
  forall theta P,
    support (push_all P theta) = support theta.
Proof.
  unfold push_all; repeat step || rewrite support_map_values.
Qed.

Lemma strictly_positive_topen:
  forall T vars k X,
    strictly_positive T vars ->
    ~(X ∈ vars) ->
    strictly_positive (topen k T (fvar X type_var)) vars.
Proof.
  eauto using strictly_positive_topen_aux.
Qed.

Definition pre_interpretation := list (nat * (tree -> tree -> Prop)).

Fixpoint forall_implies (P: tree -> Prop) (pre_theta: pre_interpretation) (theta: interpretation) :=
  match pre_theta, theta with
  | nil, nil => True
  | (X,pre_rc) :: pre_theta', (Y,rc) :: theta' =>
      X = Y /\
      forall_implies P pre_theta' theta' /\
      forall (v: tree), (forall a, P a -> pre_rc a v) -> rc v
  | _, _ => False
  end.

Lemma forall_implies_apply:
  forall P pre_theta theta X pre_rc rc v,
    forall_implies P pre_theta theta ->
    lookup Nat.eq_dec pre_theta X = Some pre_rc ->
    lookup Nat.eq_dec theta X = Some rc ->
    (forall a, P a -> pre_rc a v) ->
    rc v.
Proof.
  induction pre_theta; destruct theta; repeat step || eapply_any.
Qed.

Ltac t_forall_implies_apply :=
  match goal with
  | H1: forall_implies ?P ?ptheta ?theta,
    H2: lookup _ ?ptheta ?X = Some ?prc,
    H3: lookup _ ?theta ?X = Some ?rc |- ?rc ?v =>
    apply (forall_implies_apply _ _ _ _ _ _ _ H1 H2 H3)
  end.

Lemma forall_implies_support:
  forall P pre_theta theta,
    forall_implies P pre_theta theta ->
    support pre_theta = support theta.
Proof.
  induction pre_theta; destruct theta; repeat step || f_equal.
Qed.

Ltac t_forall_implies_support :=
  match goal with
  | H: forall_implies ?P ?ptheta ?theta |- _ =>
    poseNew (Mark (ptheta,theta) "forall_implies_suppoft");
    pose proof (forall_implies_support _ _ _ H)
  end.

Lemma forall_implies_equiv:
  forall P1 P2 ptheta theta,
    forall_implies P1 ptheta theta ->
    (forall x, P1 x <-> P2 x) ->
    forall_implies P2 ptheta theta.
Proof.
  induction ptheta; destruct theta; steps; eauto with eapply_any.
Qed.

Ltac t_forall_implies_equiv :=
  match goal with
  | H1: forall_implies ?P1 ?ptheta ?theta |- forall_implies _ ?ptheta ?theta =>
      apply forall_implies_equiv with P1
  end.

Lemma strictly_positive_append_aux:
  forall n T vars1 vars2,
    type_nodes T < n ->
    strictly_positive T vars1 ->
    strictly_positive T vars2 ->
    strictly_positive T (vars1 ++ vars2).
Proof.
  induction n; destruct T;
    repeat omega || step || destruct_tag || simp_spos || apply_any;
      eauto using no_type_fvar_append.
Qed.

Lemma strictly_positive_append:
  forall T vars1 vars2,
    strictly_positive T vars1 ->
    strictly_positive T vars2 ->
    strictly_positive T (vars1 ++ vars2).
Proof.
  eauto using strictly_positive_append_aux.
Qed.

Lemma strictly_positive_cons:
  forall T X vars,
    strictly_positive T (X :: nil) ->
    strictly_positive T vars ->
    strictly_positive T (X :: vars).
Proof.
  intros.
  change (X :: vars) with ((X :: nil) ++ vars);
    eauto using strictly_positive_append.
Qed.

Lemma strictly_positive_topen2:
  forall T k X vars,
    ~(X ∈ vars) ->
    strictly_positive T vars ->
    strictly_positive (topen k T (fvar X type_var)) (X :: nil) ->
    strictly_positive (topen k T (fvar X type_var)) (X :: vars).
Proof.
  intros; apply strictly_positive_cons;
    repeat step || apply strictly_positive_topen.
Qed.

Lemma strictly_positive_rename_one:
  forall T X Y vars,
    strictly_positive (topen 0 T (fvar X type_var)) (X :: vars) ->
    ~(X ∈ pfv T type_var) ->
    ~(Y ∈ pfv T type_var) ->
    strictly_positive (topen 0 T (fvar Y type_var)) (Y :: vars).
Proof.
  intros.
  apply strictly_positive_rename with (topen 0 T (fvar X type_var)) (X :: vars) ((X,Y) :: idrel (pfv T type_var));
    repeat step || apply equal_with_relation_topen || unfold similar_sets || rewrite swap_idrel in * || t_idrel_lookup2;
    eauto using equal_with_idrel.
Qed.

Lemma strictly_positive_no_fv:
  forall T vars,
    is_erased_type T ->
    (forall X, X ∈ pfv T type_var -> False) ->
    strictly_positive T vars.
Proof.
  intros.
  apply no_type_fvar_strictly_positive; repeat step || unfold no_type_fvar; eauto.
Qed.
