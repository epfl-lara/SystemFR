Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Equations.Equations.

Require Import Termination.Sets.
Require Import Termination.Tactics.
Require Import Termination.Syntax.
Require Import Termination.TermList.
Require Import Termination.SmallStep.
Require Import Termination.AssocList.
Require Import Termination.EquivalenceLemmas.
Require Import Termination.ListUtils.
Require Import Termination.SubstitutionLemmas.
Require Import Termination.StarRelation.
Require Import Termination.SizeLemmas.
Require Import Termination.StarLemmas.
Require Import Termination.TypeErasure.
Require Import Termination.SubstitutionErase.
Require Import Termination.TreeLists.
Require Import Termination.TermListReducible.
Require Import Termination.StarInversions.
Require Import Termination.EquivalentWithRelation.
Require Import Termination.EqualWithRelation.
Require Import Termination.TermProperties.
Require Import Termination.ErasedTermLemmas.
Require Import Termination.OpenTOpen.
Require Import Termination.StarInversions.

Require Import Termination.Equivalence.
Require Import Termination.EquivalenceLemmas.

Require Import Termination.ReducibilityCandidate.
Require Import Termination.ReducibilityDefinition.
Require Import Termination.ReducibilityLemmas.
Require Import Termination.ReducibilityRenaming.
Require Import Termination.ReducibilityUnused.
Require Import Termination.ReducibilitySubst.
Require Import Termination.ReducibilityRecRules.
Require Import Termination.ReducibilityNatRules.
Require Import Termination.RedTactics.

Require Import Termination.Freshness.

Require Import Termination.WFLemmas.
Require Import Termination.FVLemmasLists.
Require Import Termination.WFLemmasLists.

Require Import Termination.StrictPositivity.
Require Import Termination.StrictPositivityLemmas.
Require Import Termination.StrictPositivityLemma.
Require Import Termination.StrictPositivityPush.
Require Import Termination.StrictPositivityPull.

Require Import Omega.

Opaque reducible_values.
Opaque strictly_positive.
Opaque makeFresh.

Fixpoint build_nat (n: nat): tree :=
  match n with
  | 0 => zero
  | S n => succ (build_nat n)
  end.

(*
Definition generalizes T :=
  forall theta t,
    reducible_values theta t (intersect T) <->
    (exists n, forall m, m >= n -> reducible_values theta t (T_rec (build_nat m) T_top T)).

Lemma generalizes_expr:
  forall T theta t,
    generalizes T ->
    valid_interpretation theta ->
    reducible theta t (intersect T) <->
    (exists n, forall m, m >= n -> reducible theta t (T_rec (build_nat m) T_top T)).
Proof.
  unfold generalizes, reducible, reduces_to; steps.
  - rewrite H in *; steps; eauto 6.
  - eapply_any; eauto.
  - unshelve epose proof (H1 n _); steps.
    eexists; steps; eauto.
    apply H; steps.
    exists n; steps.
    unshelve epose proof (H1 m _); repeat step || t_deterministic_star;
      eauto using red_is_val.
Qed.
*)

Set Program Mode.

Definition intersect T0 Ts := T_forall T_nat (T_rec (lvar 0 term_var) T0 Ts).

Lemma fold_in_intersect:
  forall theta t T0 Ts,
    wf T0 0 ->
    wf Ts 0 ->
    valid_interpretation theta ->
    reducible_values theta t (intersect T0 Ts) ->
    exists v, closed_value v /\ t = tfold v.
Proof.
  unfold intersect;
    repeat match goal with
           | H: reducible_values _ _ (T_forall _ _) |- _ => simp reducible_values in H
           | _ => step || (rewrite open_none in * by steps)
           | H: _ |- _  => apply fold_in_rec with theta T0 (open 0 Ts (succ zero)) zero
           | H: forall a, _ -> _ |-  _ =>
               poseNew (Mark 0 "once");
               unshelve epose proof (H (succ zero) _ _)
           | _ => simp reducible_values
           end.
Qed.

Ltac t_fold_in_intersect :=
  match goal with
  | H1: valid_interpretation ?theta, H2: reducible_values ?theta ?t (intersect ?T0 ?Ts) |- _ =>
     is_var t;
     unshelve epose proof (fold_in_intersect theta t T0 Ts _ _ H1 H2)
  end.

Lemma non_empty_nat:
  forall theta, non_empty theta T_nat.
Proof.
  unfold non_empty; intros; exists zero; repeat step || simp_red.
Qed.

Ltac t_instantiate_reducible3 :=
  match goal with
  | H1: reducible_values _ ?v ?T, H3: forall a, _ -> _ -> _ |- _ =>
    poseNew (Mark (v,H3) "t_instantiate_reducible");
    unshelve epose proof (H3 v _ H1)
  end.

Lemma reducible_values_unfold_gen:
  forall T0 Ts theta v X,
    wf T0 0 ->
    wf Ts 0 ->
    twf T0 0 ->
    twf Ts 1 ->
    ~(X ∈ pfv Ts type_var) ->
    strictly_positive (topen 0 Ts (fvar X type_var)) (X :: nil) ->
    is_erased_type T0 ->
    is_erased_type Ts ->
    valid_interpretation theta ->
    reducible_values theta (tfold v) (intersect T0 Ts) ->
    reducible_values theta v (topen 0 Ts (intersect T0 Ts)).
Proof.
  unfold intersect in *; repeat step.
  apply strictly_positive_push_forall2 with X;
    repeat match goal with
           | H: reducible_values _ _ (T_forall _ _) |- _ => simp reducible_values in H
           | H: reducible_values _ _ (T_rec _ _ _) |- _ => simp reducible_values in H
           | H1: reducible_values _ ?v T_nat, H3: forall a, _ -> _ -> _ |- _ =>
             poseNew (Mark (v,H3) "t_instantiate_reducible");
             unshelve epose proof (H3 (succ v) _ _)
           | _ => step || (rewrite open_none in * by steps) || apply reducible_values_succ
           end;
      eauto using non_empty_nat;
      eauto with berased;
      try solve [ t_closing ];
      eauto 3 using smallstep_succ_zero with falsity.

  apply reducibility_subst_head in H19;
    repeat step || t_invert_star || t_listutils ||
           (rewrite is_erased_term_tfv in H15 by (eauto with berased));
      eauto with btwf bwf.

  lazymatch goal with
  | H: star small_step ?v1 ?v2 |- _ =>
    unshelve epose proof (star_smallstep_value v1 v2 H _); clear H2
  end;
    repeat step || t_listutils;
    eauto with values.
Qed.

Lemma reducible_unfold_gen:
  forall T0 Ts theta t X,
    wf T0 0 ->
    wf Ts 0 ->
    twf T0 0 ->
    twf Ts 1 ->
    ~(X ∈ pfv Ts type_var) ->
    strictly_positive (topen 0 Ts (fvar X type_var)) (X :: nil) ->
    is_erased_type T0 ->
    is_erased_type Ts ->
    valid_interpretation theta ->
    reducible theta t (intersect T0 Ts) ->
    reducible theta (tunfold t) (topen 0 Ts (intersect T0 Ts)).
Proof.
  unfold reducible, reduces_to;
    repeat step || t_fold_in_intersect.
  exists v; repeat step || apply star_unfold_fold;
    try solve [ t_closing ];
    eauto using reducible_values_unfold_gen.
Qed.

Definition decreasing theta T0 Ts :=
  forall v, reducible_values theta v (topen 0 Ts (T_rec zero T0 Ts)) -> reducible_values theta v T0.

Lemma reducible_values_fold_gen:
  forall T0 Ts theta v X,
    wf T0 0 ->
    wf Ts 0 ->
    twf T0 0 ->
    twf Ts 1 ->
    ~(X ∈ pfv Ts type_var) ->
    strictly_positive (topen 0 Ts (fvar X type_var)) (X :: nil) ->
    is_erased_type T0 ->
    is_erased_type Ts ->
    valid_interpretation theta ->
    decreasing theta T0 Ts ->
    reducible_values theta v (topen 0 Ts (intersect T0 Ts)) ->
    reducible_values theta (tfold v) (intersect T0 Ts).
Proof.
  unfold intersect in *; repeat step.
  simp reducible_values; repeat step || (rewrite open_none in * by steps); try solve [ t_closing ].

  unshelve epose proof (strictly_positive_pull_forall2 _ _ _ _ _ X _ _ _ H9);
    repeat step; eauto using non_empty_nat.

  destruct a; repeat step || simp_red;
    try solve [ t_closing ];
    eauto with smallstep.
  - (* case a = 0, we use the decreasing property *)
    left; exists v; repeat step. unfold decreasing in *; repeat step || apply_any.
    unshelve epose proof (H11 zero _);
      repeat step || simp_red || rewrite open_none in * by steps.
  - (* case a = n+1 *)
    right; exists a, v, (makeFresh (
                     support theta ::
                     pfv a type_var ::
                     pfv T0 type_var ::
                     pfv Ts type_var ::
                     (X :: nil) ::
                     nil));
    repeat step;
    try finisher.

    apply reducibility_subst_head2;
      repeat step || t_listutils;
      try finisher;
      eauto with bwf btwf.

    unshelve epose proof (H11 a _); repeat step || simp_red || rewrite open_none in * by steps.
Qed.

Lemma reducible_fold_gen:
  forall T0 Ts theta t X,
    wf T0 0 ->
    wf Ts 0 ->
    twf T0 0 ->
    twf Ts 1 ->
    ~(X ∈ pfv Ts type_var) ->
    strictly_positive (topen 0 Ts (fvar X type_var)) (X :: nil) ->
    is_erased_type T0 ->
    is_erased_type Ts ->
    valid_interpretation theta ->
    decreasing theta T0 Ts ->
    reducible theta t (topen 0 Ts (intersect T0 Ts)) ->
    reducible theta (tfold t) (intersect T0 Ts).
Proof.
  unfold reducible, reduces_to;
    repeat step.
  exists (tfold t'); repeat step;
    try solve [ t_closing ];
    eauto using reducible_values_fold_gen;
    eauto with bsteplemmas.
Qed.
