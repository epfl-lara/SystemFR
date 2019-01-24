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

Require Import Termination.FVLemmasLists.
Require Import Termination.WFLemmasLists.

Require Import Omega.

Opaque reducible_values.
Opaque makeFresh.

Fixpoint build_nat (n: nat): tree :=
  match n with
  | 0 => zero
  | S n => succ (build_nat n)
  end.


Definition intersect T := T_forall T_nat (T_rec (lvar 0 term_var) T_top T).

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

Set Program Mode.

Lemma red_one:
  forall theta, reducible_values theta (succ zero) T_nat.
Proof.
  repeat step || simp_red.
Qed.

Ltac inst_one :=
  match goal with
  | H: forall a, reducible_values ?theta _ T_nat -> _ |- _ =>
      poseNew (Mark 0 "once"); unshelve epose proof (H (succ zero) (red_one theta))
  end.

Lemma small_step_one_zero:
  star small_step (succ zero) zero ->
  False.
Proof.
  intro H; unshelve epose proof (star_smallstep_value _ _ H _); steps.
Qed.

Lemma star_unfold_fold:
  forall t v,
    closed_value (tfold v) ->
    star small_step t (tfold v) ->
    star small_step (tunfold t) v.
Proof.
  unfold closed_value.
  repeat step || step_inversion is_value.
  eapply star_smallstep_trans; eauto with bsteplemmas; eauto with smallstep.
Qed.

Ltac t_reducible_unfold :=
  match goal with
  | _ => progress (unfold closed_value in *)
  | _ => apply star_unfold_fold
  | H: star small_step (succ zero) zero |- _ => apply (False_ind _ (small_step_one_zero H))
  | H: star small_step ?t (tfold ?v) |- exists t', star small_step (tunfold ?t) _ /\ _ => exists v
  | H: singleton _ = nil |- _ => inversion H
  | H: reducible_values _ _ (intersect _) |- _ => simp reducible_values in H
  | H: reducible_values _ _ (T_rec (succ zero) _ _) |- _ => simp reducible_values in H
  | _ => step || inst_one
  end.

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
    generalizes T ->
    reducible theta t (intersect T) ->
    reducible theta (tunfold t) (topen 0 T (intersect T)).
Proof.
  unfold reducible, reduces_to; induction T; repeat t_reducible_unfold.
Admitted.
