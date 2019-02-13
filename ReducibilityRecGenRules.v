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

Require Import Termination.Equivalence.
Require Import Termination.EquivalenceLemmas.

Require Import Termination.ReducibilityCandidate.
Require Import Termination.ReducibilityDefinition.
Require Import Termination.ReducibilityLemmas.
Require Import Termination.ReducibilityRenaming.
Require Import Termination.ReducibilityUnused.
Require Import Termination.ReducibilitySubst.
Require Import Termination.ReducibilityRecRules.
Require Import Termination.RedTactics.

Require Import Termination.Freshness.

Require Import Termination.WFLemmas.
Require Import Termination.FVLemmasLists.
Require Import Termination.WFLemmasLists.

Require Import Termination.StrictPositivity.
Require Import Termination.StrictPositivityLemma.
Require Import Termination.StrictPositivityPush.
Require Import Termination.StrictPositivityPull.

Require Import Omega.

Opaque reducible_values.
Opaque makeFresh.

Fixpoint build_nat (n: nat): tree :=
  match n with
  | 0 => zero
  | S n => succ (build_nat n)
  end.

Definition intersect T0 Ts := T_forall T_nat (T_rec (lvar 0 term_var) T0 Ts).

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

Lemma fold_in_intersect:
  forall theta t T,
    valid_interpretation theta ->
    reducible_values theta t (intersect T) ->
    exists v, closed_value v /\ t = tfold v.
Proof.
  unfold intersect;
    repeat match goal with
           | H: reducible_values _ _ (T_forall _ _) |- _ => simp reducible_values in H
           | _ => step
           | H: _ |- _  => apply fold_in_rec with theta T_top (open 0 T (succ zero)) zero
           | H: forall a, _ -> _ |-  _ =>
               poseNew (Mark 0 "once");
               unshelve epose proof (H (succ zero) _ _)
           | _ => simp reducible_values
           end.
Qed.

Ltac t_reducible_unfold :=
  match goal with
  | _ => progress (unfold closed_value in *)
  | _ => apply star_unfold_fold
  | H: star small_step ?t (tfold ?v) |- exists t', star small_step (tunfold ?t) _ /\ _ => exists v
  | H: singleton _ = nil |- _ => inversion H
(*  | H: reducible_values _ _ (intersect _) |- _ => simp reducible_values in H
  | H: reducible_values _ _ (T_rec (succ zero) _ _) |- _ => simp reducible_values in H *)
  | _ => step || inst_one
  | H1: valid_interpretation ?theta, H2: reducible_values ?theta ?t (intersect ?T) |- _ =>
     is_var t; pose proof (fold_in_intersect theta t T H1 H2)
  | _ => rewrite_any
  end.

Lemma reducible_values_unfold_gen:
  forall T0 Ts theta v n X,
    wf n 0 ->
    twf n 0 ->
    wf T0 0 ->
    twf T0 1 ->
    wf Ts 0 ->
    twf Ts 1 ->
    ~(X ∈ pfv T type_var) ->
    strictly_positive (topen 0 T (fvar X type_var)) (X :: nil) ->
    is_erased_term n ->
    is_erased_type T ->
    valid_interpretation theta ->
    reducible_values theta (tfold v) (intersect T0 Ts) ->
    reducible_values theta v (topen 0 T (intersect T0 Ts)).
Proof.
  unfold intersect in *; repeat step.
(*  apply strictly_positive_push_forall; steps.
  simp reducible_values in H8; steps.
  evar (a: term).
  unshelve epose proof (H10 (succ a) _) as HH; steps.
  - admit.
  - admit.
  - simp reducible_values in HH; steps.
    + admit.
    + apply reducibility_subst_head in H17; steps.
      * rewrite open_none in * by t_rewrite.
Admitted.
*)
Admitted.


(*
  - admit.
  - admit.
  - simp reducible_values in H10; steps.
    + admit.
    + apply reducibility_subst_head in H17; steps.
    rewrite open_topen in H17; repeat step || (rewrite open_none in * by t_rewrite); eauto with btwf. admit.

  
(*  assert (reducible_values theta v (T_forall T_nat (topen 0 T (T_rec (lvar 0 term_var) T_top T)))). { *)
  
    repeat match goal with
           | H: reducible_values _ _ (T_forall _ _) |- _ => simp reducible_values in H
           | H2: reducible_values _ ?a T_nat, H: forall a, _ -> _ |-  _ =>
               poseNew (Mark H "instantiate once");
               unshelve epose proof (H (succ a) _)
           | _ =>
             step || simp reducible_values || unfold closed_term in * ||
             t_reducible_values_closed || unfold closed_value in * ||
             step_inversion is_value ||
             
             (rewrite open_none in * by t_rewrite)
           | H: reducible_values _ _ T_nat |- _ => simp reducible_values in H
           | H: reducible_values ?theta (tfold ?v) (T_rec (succ ?n) ?T0 ?Ts) |- _ =>
               poseNew (Mark H "red_once");
               unshelve epose proof
                 (reducible_values_unfold theta v n T0 Ts _ _ _ _ _ _ _ _ _ _ H)
           end;
      eauto with btwf.
    rewrite open_topen; repeat step || (rewrite open_none in * by t_rewrite); eauto with btwf. admit.
    lazymatch goal with
                 | H: _ |- _ =>
               poseNew (Mark H "red_once");
               apply reducible_values_unfold in H
    end.
    apply reducible_values_unfold in H11.
  }
  repeat t_reducible_unfold; eauto with values.
  repeat rewrite_any.
  - rewrite H7 in *.
*)

Lemma reducible_unfold:
  forall T theta t n,
    wf n 0 ->
    twf n 0 ->
    wf T 0 ->
    twf T 1 ->
    pfv T type_var = nil ->
    is_erased_term n ->
    is_erased_type T ->
    valid_interpretation theta ->
    reducible theta t (intersect T) ->
    reducible theta (tunfold t) (topen 0 T (intersect T)).
Proof.
  unfold reducible, reduces_to; repeat t_reducible_unfold; eauto with values.
  repeat rewrite_any.
(*  - rewrite H7 in *. *)
Admitted.
