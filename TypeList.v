Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Require Import Termination.Syntax.
Require Import Termination.Sets.
Require Import Termination.AssocList.
Require Import Termination.Tactics.
Require Import Termination.SubstitutionLemmas.
Require Import Termination.ListUtils.

Open Scope list_scope.

Fixpoint closed_types (ltypes: list (nat * term)): Prop :=
  match ltypes with
  | nil => True
  | (_, T) :: Ts => closed_types Ts /\ wf T 0 /\ fv T = nil
  end.
