Require Import Coq.Strings.String.

Require Import Termination.Syntax.
Require Import Termination.Tactics.
Require Import Termination.Freshness.
Require Import Termination.FVLemmas.
Require Import Termination.ListUtils.
Require Import Termination.SubstitutionLemmas.
Require Import Termination.TermList.
Require Import Termination.TermListLemmas.
Require Import Termination.AssocList.
Require Import Termination.TypeErasure.
Require Import Termination.FVLemmasLists.
Require Import Termination.EquivalenceLemmas.
Require Import Termination.SubstitutionErase.
Require Import Termination.TreeLists.
Require Import Termination.TermListReducible.
Require Import Termination.ErasedTermLemmas.
Require Import Termination.StarRelation.
Require Import Termination.SmallStep.

Require Import Termination.ReducibilityCandidate.
Require Import Termination.ReducibilityDefinition.
Require Import Termination.ReducibilityLemmas.
Require Import Termination.ReducibilityRenaming.

Ltac t_reducible_rename_one :=
  match goal with
  | H: reducible_values ((?X,?RC) :: ?theta) ?v (topen 0 ?T (fvar ?X type_var)) |-
       reducible_values ((?Y,?RC) :: ?theta) ?v (topen 0 ?T (fvar ?Y type_var)) =>
    apply reducible_rename_one with X
  end.
