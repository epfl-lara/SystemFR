Require Import Coq.Strings.String.

Require Export SystemFR.Syntax.
Require Export SystemFR.Tactics.
Require Export SystemFR.Freshness.
Require Export SystemFR.FVLemmas.
Require Export SystemFR.ListUtils.
Require Export SystemFR.SubstitutionLemmas.
Require Export SystemFR.TermList.
Require Export SystemFR.TermListLemmas.
Require Export SystemFR.AssocList.
Require Export SystemFR.FVLemmasLists.
Require Export SystemFR.EquivalentStar.
Require Export SystemFR.SubstitutionErase.
Require Export SystemFR.TreeLists.
Require Export SystemFR.TermListReducible.
Require Export SystemFR.ErasedTermLemmas.
Require Export SystemFR.RelationClosures.
Require Export SystemFR.SmallStep.

Require Export SystemFR.ReducibilityCandidate.
Require Export SystemFR.ReducibilityDefinition.
Require Export SystemFR.ReducibilityLemmas.
Require Export SystemFR.ReducibilityRenaming.

Ltac t_reducible_rename_one :=
  match goal with
  | H: reducible_values ((?X,?RC) :: ?theta) ?v (topen 0 ?T (fvar ?X type_var)) |-
       reducible_values ((?Y,?RC) :: ?theta) ?v (topen 0 ?T (fvar ?Y type_var)) =>
    apply reducible_rename_one with X
  end.
