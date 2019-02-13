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
Require Import Termination.StrictPositivityLemma.

Require Import Termination.FVLemmas.

Opaque makeFresh.
Opaque Nat.eq_dec.
Opaque reducible_values.
Opaque strictly_positive.

Lemma strictly_positive_pull_forall:
  forall T theta theta' A v X a,
    ~(X ∈ pfv T type_var) ->
    non_empty theta A ->
    strictly_positive (topen 0 T (fvar X type_var)) (X :: nil) ->
    reducible_values v (topen 0 T (T_forall A B)) ->
    reducible_values theta a A ->
    reducible_values v (topen 0 T (open 0 B a))).
Proof.
Admitted.