Require Import Coq.Strings.String.

Require Import SystemFR.AssocList.
Require Import SystemFR.Tactics.
Require Import SystemFR.Sets.
Require Import SystemFR.Trees.
Require Import SystemFR.Syntax.
Require Import SystemFR.ListUtils.

Require Import PeanoNat.

Open Scope list_scope.

Fixpoint equivalent_pairs_with_relation { T } rel (l1 l2: map nat T) equiv :=
  match l1, l2 with
  | nil, nil => True
  | (x,a) :: l1', (y,b) :: l2' =>
    lookup Nat.eq_dec rel x = Some y /\
    lookup Nat.eq_dec (swap rel) y = Some x /\
    equiv a b /\
    equivalent_pairs_with_relation rel l1' l2' equiv
  | _, _ => False
  end.
