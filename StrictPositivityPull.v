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
Require Import Termination.StrictPositivity.
Require Import Termination.StrictPositivityPush.

Require Import Termination.FVLemmas.

Opaque makeFresh.
Opaque Nat.eq_dec.
Opaque reducible_values.
Opaque strictly_positive.

Ltac apply_induction_pull H :=
  match goal with
  | H1: non_empty ?theta ?A,
    H2: forall_implicate _ ?ptheta ?theta' |- reducible_values (?theta' ++ _) _ ?T =>
      apply H with (size T, index T) ptheta A
  end.

(*
Lemma strictly_positive_push_forall:
  forall measure T pre_theta theta theta' A v,
    (size T, index T) = measure ->
    wf T 0 ->
    twf T 0 ->
    wf A 0 ->
    twf A 0 ->
    valid_interpretation theta ->
    valid_interpretation theta' ->
    non_empty theta A ->
    valid_pre_interpretation (fun a => reducible_values theta a A) pre_theta ->
    strictly_positive T (support theta') ->
    is_erased_type A ->
    is_erased_type T ->
    (forall a,
      reducible_values theta a A ->
      reducible_values (push_one a pre_theta ++ theta) v T) ->
    forall_implicate (fun a => reducible_values theta a A) pre_theta theta' ->
    reducible_values (theta' ++ theta) v T.
Proof.
*)
