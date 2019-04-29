Require Import Coq.Strings.String.

Require Import SystemFR.Syntax.
Require Import SystemFR.Tactics.
Require Import SystemFR.Freshness.
Require Import SystemFR.FVLemmas.
Require Import SystemFR.ListUtils.
Require Import SystemFR.SubstitutionLemmas.
Require Import SystemFR.TermList.
Require Import SystemFR.TermListLemmas.
Require Import SystemFR.AssocList.
Require Import SystemFR.FVLemmasLists.
Require Import SystemFR.EquivalenceLemmas.
Require Import SystemFR.SubstitutionErase.
Require Import SystemFR.TreeLists.
Require Import SystemFR.TermListReducible.
Require Import SystemFR.ErasedTermLemmas.
Require Import SystemFR.StarRelation.
Require Import SystemFR.SmallStep.

Require Import SystemFR.ReducibilityCandidate.
Require Import SystemFR.ReducibilityDefinition.
Require Import SystemFR.ReducibilityLemmas.
Require Import SystemFR.ReducibilityRenaming.

Ltac t_reducible_rename_one :=
  match goal with
  | H: reducible_values ((?X,?RC) :: ?theta) ?v (topen 0 ?T (fvar ?X type_var)) |-
       reducible_values ((?Y,?RC) :: ?theta) ?v (topen 0 ?T (fvar ?Y type_var)) =>
    apply reducible_rename_one with X
  end.
