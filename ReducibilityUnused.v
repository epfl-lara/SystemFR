Require Import Equations.Equations.

Require Import Coq.Strings.String.

Require Import Termination.Syntax.
Require Import Termination.Tactics.
Require Import Termination.Sets.
Require Import Termination.TermList.
Require Import Termination.AssocList.
Require Import Termination.SizeLemmas.
Require Import Termination.ListUtils.
Require Import Termination.SmallStep.
Require Import Termination.StarRelation.
Require Import Termination.SubstitutionLemmas.
Require Import Termination.TypeErasure.
Require Import Termination.TypeErasureLemmas.
Require Import Termination.Freshness.
Require Import Termination.EquivalentWithRelation.
Require Import Termination.IdRelation.

Require Import Termination.FVLemmas.
Require Import Termination.FVLemmasLists.

Require Import Termination.ReducibilityCandidate.
Require Import Termination.ReducibilityDefinition.
Require Import Termination.ReducibilityLemmas.
Require Import Termination.ReducibilityRenaming.

Require Import PeanoNat.

Open Scope list_scope.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducible_unused2:
  forall t T (X : nat) (theta : interpretation) (RC : tree -> Prop),
    (X ∈ pfv T type_var -> False) ->
    valid_interpretation theta ->
    reducibility_candidate RC ->
    reducible_values theta t T ->
    reducible_values ((X, RC) :: theta) t T.
Proof.
  intros.
  unshelve epose proof (reducible_rename T T t theta ((X,RC) :: theta) (idrel (pfv T type_var)) _ _ _ _ _); repeat step || apply equivalent_with_idrel || apply equal_with_idrel.
Qed.

Lemma reducible_unused3:
  forall t T (X : nat) (theta : interpretation) (RC : tree -> Prop),
    reducible_values ((X, RC) :: theta) t T ->
    (X ∈ pfv T type_var -> False) ->
    valid_interpretation theta ->
    reducibility_candidate RC ->
    reducible_values theta t T.
Proof.
  intros.
  unshelve epose proof (reducible_rename T T t ((X,RC) :: theta) theta (idrel (pfv T type_var)) _ _ _ _ _);    repeat step || apply equivalent_with_idrel2 || apply equal_with_idrel.
Qed.

Lemma satisfies_unused:
  forall (gamma : list (nat * tree)) lterms (X : nat) (theta : interpretation) RC,
    (X ∈ pfv_context gamma type_var -> False) ->
    valid_interpretation theta ->
    reducibility_candidate RC ->
    satisfies (reducible_values theta) gamma lterms ->
    satisfies (reducible_values ((X, RC) :: theta)) gamma lterms.
Proof.
  induction gamma as [ | [ x T ] gamma' IH ]; destruct lterms;
    repeat step || t_termlist || step_inversion satisfies || t_listutils ||
           apply SatCons || apply reducible_unused2 ||
           (rewrite fv_subst_different_tag in * by (steps; eauto with bfv)).
Qed.
